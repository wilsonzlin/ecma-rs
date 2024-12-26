use ahash::{HashMap, HashSet};
use parse_js::{ast::Syntax, loc::Loc, visit::{JourneyControls, Visitor}};
use parse_js::ast::node::Node;
use symbol_js::symbol::{Scope, ScopeType, Symbol};

// Four tasks (fill out each field as appropriate).
#[derive(Default)]
struct VarVisitor {
  declared: HashSet<Symbol>,
  foreign: HashSet<Symbol>,
  unknown: HashSet<String>,
  use_before_decl: HashMap<Symbol, Loc>,

  in_var_decl: bool,
  in_var_decl_stack: Vec<bool>,
}

// The lifted scope is the nearest self-or-ancestor scope that is not a block, or the self-or-ancestor scope just below the global scope.
// This is useful as we don't want a usage in an inner block to count as "foreign".
fn lifted_scope(scope: &Scope) -> Scope {
  if scope.data().typ() != ScopeType::Block {
    return scope.clone();
  };
  let scope_data = scope.data();
  let parent = scope_data.parent().unwrap();
  if parent.data().typ() == ScopeType::Global {
    return scope.clone();
  };
  lifted_scope(parent)
}

impl Visitor for VarVisitor {
  fn on_syntax_down(&mut self, node: &Node, ctl: &mut JourneyControls) {
    match node.stx.as_ref() {
      Syntax::VarDecl { .. } => {
        self.in_var_decl_stack.push(self.in_var_decl);
        self.in_var_decl = true;
      }
      Syntax::IdentifierExpr { name } => {
        let usage_scope = node.assoc.get::<Scope>().unwrap();
        let usage_ls = lifted_scope(usage_scope);
        match usage_scope.find_symbol_up_to_with_scope(name.clone(), |_| false) {
          None => {
            // Unknown.
            self.unknown.insert(name.clone());
          }
          Some((decl_scope, symbol)) => {
            let decl_ls = lifted_scope(&decl_scope);
            if usage_ls != decl_ls {
              self.foreign.insert(symbol);
            } else if !self.declared.contains(&symbol) {
              // Check for use before declaration to ensure strict SSA.
              // NOTE: This doesn't check across closures, as that is mostly a runtime determination (see symbol-js/examples/let.js), but we don't care as those are foreign vars and don't affect strict SSA (i.e. correctness).
              self.use_before_decl.insert(symbol, node.loc);
            }
          }
        };
      }
      Syntax::ClassOrFunctionName { name } => {
        let scope = node.assoc.get::<Scope>().unwrap();
        // It won't exist if it's a global declaration.
        // TODO Is this the only time it won't exist (i.e. is it always safe to ignore None)?
        if let Some(symbol) = scope.find_symbol(name.clone()) {
          assert!(self.declared.insert(symbol));
        };
      }
      // An identifier pattern doesn't always mean declaration e.g. simple assignment.
      Syntax::IdentifierPattern { name } if self.in_var_decl => {
        let scope = node.assoc.get::<Scope>().unwrap();
        // It won't exist if it's a global declaration.
        // TODO Is this the only time it won't exist (i.e. is it always safe to ignore None)?
        if let Some(symbol) = scope.find_symbol(name.clone()) {
          assert!(self.declared.insert(symbol));
        };
      }
      _ => {}
    }
  }

  fn on_syntax_up(&mut self, node: &Node) {
      match node.stx.as_ref() {
        Syntax::VarDecl { .. } => {
          self.in_var_decl = self.in_var_decl_stack.pop().unwrap();
        }
        _ => {}
      }
  }
}

#[derive(Default)]
pub struct VarAnalysis {
  pub declared: HashSet<Symbol>,
  pub foreign: HashSet<Symbol>,
  pub unknown: HashSet<String>,
  pub use_before_decl: HashMap<Symbol, Loc>,
}

impl VarAnalysis {
  pub fn analyze(top_level_node: &Node) -> Self {
    let mut var_visitor = VarVisitor::default();
    var_visitor.visit(top_level_node);
    Self {
      declared: var_visitor.declared,
      foreign: var_visitor.foreign,
      unknown: var_visitor.unknown,
      use_before_decl: var_visitor.use_before_decl,
    }
  }
}

#[cfg(test)]
mod tests {
  use ahash::{HashMap, HashMapExt, HashSet};
  use parse_js::{parse, visit::Visitor};
  use symbol_js::{
      compute_symbols,
      symbol::{Scope, ScopeType, Symbol},
      TopLevelMode,
  };

  use super::VarVisitor;

  fn parse_and_visit(source: &[u8]) -> (Scope, VarVisitor) {
    let mut parsed = parse(source).unwrap();
    let top_level_scope = compute_symbols(&mut parsed, TopLevelMode::Global);
    let mut var_visitor = VarVisitor::default();
    var_visitor.visit(&parsed);
    (top_level_scope, var_visitor)
  }

  struct T {
    typ: ScopeType,
    // Record the symbol ID of .0 into the returned map at entry with key .1.
    syms: Vec<(&'static str, &'static str)>,
    children: Vec<T>,
  }

  fn test_scope_tree(out: &mut HashMap<&'static str, Symbol>, s: &Scope, m: &T) {
    let sd = s.data();
    assert_eq!(sd.typ(), m.typ);
    assert_eq!(sd.symbol_count(), m.syms.len());
    for (s, k) in m.syms.iter() {
      let Some(sym) = sd.get_symbol(s) else {
        panic!("did not find the declaration for {s}")
      };
      assert!(out.insert(k, sym).is_none());
    }
    assert_eq!(sd.children().len(), m.children.len());
    for (i, c) in sd.children().iter().enumerate() {
      test_scope_tree(out, c, &m.children[i]);
    }
  }

  #[test]
  fn test_var_visitor() {
    let (s, v) = parse_and_visit(
      br#"
        (() => {
          let a, b;
          z;
          (() => {
            let c;
            y, b, c;
            (() => {
              let b;
              z, y, x, a;
              {
                let d;
                b, w;
                {
                  let e;
                  z, w, c, b, a;
                }
              }
            })();
          })();
        })();
      "#,
    );

    // Verify the entire scope tree from the top.
    let mut syms = HashMap::new();
    #[rustfmt::skip]
    test_scope_tree(&mut syms, &s, &T {
      typ: ScopeType::Global,
      syms: vec![],
      children: vec![
        T {
          typ: ScopeType::ArrowFunction,
          syms: vec![("a", "a"), ("b", "b1")],
          children: vec![
            T {
              typ: ScopeType::ArrowFunction,
              syms: vec![("c", "c")],
              children: vec![
                T {
                  typ: ScopeType::ArrowFunction,
                  syms: vec![("b", "b2")],
                  children: vec![
                    T {
                      typ: ScopeType::Block,
                      syms: vec![("d", "d")],
                      children: vec![
                        T {
                          typ: ScopeType::Block,
                          syms: vec![("e", "e")],
                          children: vec![],
                        },
                      ],
                    },
                  ],
                },
              ],
            },
          ],
        },
      ],
    });

    // Verify the visit.
    assert_eq!(
      v.declared,
      HashSet::from_iter([
        syms["a"],
        syms["b1"],
        syms["b2"],
        syms["c"],
        syms["d"],
        syms["e"],
      ]),
    );

    assert_eq!(
      v.foreign,
      HashSet::from_iter([
        syms["a"],
        syms["b1"],
        syms["c"],
      ]),
    );

    assert_eq!(
      v.use_before_decl.keys().cloned().collect::<HashSet<_>>(),
      HashSet::from_iter([
      ]),
    );

    assert_eq!(
      v.unknown,
      HashSet::from_iter([
        "w".to_string(),
        "y".to_string(),
        "x".to_string(),
        "z".to_string(),
      ]),
    );
  }

  #[test]
  fn test_var_visitor_with_globals() {
    let source = br#"
      let globalVar;
      anotherGlobalVar, z;
      {
        a, b, z;
        let a;
        {
          a, b, c, globalVar;
          let b, c;
          {
            a, b, globalVar;
            let b, d;
            d;
          }
        }
      }
    "#;
    let (s, v) = parse_and_visit(source);

    // Verify the entire scope tree from the top.
    let mut syms = HashMap::new();
    #[rustfmt::skip]
    test_scope_tree(&mut syms, &s, &T {
      typ: ScopeType::Global,
      syms: vec![],
      children: vec![
        T {
          typ: ScopeType::Block,
          syms: vec![("a", "a")],
          children: vec![
            T {
              typ: ScopeType::Block,
              syms: vec![("b", "b1"), ("c", "c")],
              children: vec![
                T {
                  typ: ScopeType::Block,
                  syms: vec![("b", "b2"), ("d", "d")],
                  children: vec![],
                },
              ],
            },
          ],
        },
      ],
    });

    // Verify the visit.
    assert_eq!(
      v.declared,
      HashSet::from_iter([
        syms["a"],
        syms["b1"],
        syms["b2"],
        syms["c"],
        syms["d"],
      ]),
    );

    assert_eq!(
      v.foreign,
      HashSet::from_iter([
      ]),
    );

    assert_eq!(
      v.use_before_decl.keys().cloned().collect::<HashSet<_>>(),
      HashSet::from_iter([
        syms["a"],
        syms["b1"],
        syms["b2"],
        syms["c"],
      ]),
    );

    assert_eq!(
      v.unknown,
      HashSet::from_iter([
        "anotherGlobalVar".to_string(),
        "b".to_string(),
        "globalVar".to_string(),
        "z".to_string(),
      ]),
    );
  }
}
