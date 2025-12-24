use ahash::HashMap;
use ahash::HashSet;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use symbol_js::symbol::Scope;
use symbol_js::symbol::ScopeType;
use symbol_js::symbol::Symbol;

type PatDeclNode = Node<PatDecl>;
type IdExprNode = Node<IdExpr>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type IdPatNode = Node<IdPat>;

// Four tasks (fill out each field as appropriate).
#[derive(Debug, Default, VisitorMut)]
#[visitor(
  PatDeclNode,
  IdExprNode(enter),
  ClassOrFuncNameNode(enter),
  IdPatNode(enter)
)]
struct VarVisitor {
  declared: HashSet<Symbol>,
  foreign: HashSet<Symbol>,
  unknown: HashSet<String>,
  use_before_decl: HashMap<Symbol, (String, Loc)>,

  in_pat_decl_stack: Vec<bool>,
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

impl VarVisitor {
  pub fn enter_pat_decl_node(&mut self, _node: &mut Node<PatDecl>) {
    self.in_pat_decl_stack.push(true);
  }

  pub fn exit_pat_decl_node(&mut self, _node: &mut Node<PatDecl>) {
    self.in_pat_decl_stack.pop();
  }

  pub fn enter_id_expr_node(&mut self, node: &mut Node<IdExpr>) {
    let name = &node.stx.name;
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
          let start = node.loc.0.saturating_sub(name.len());
          let end = start + name.len();
          // Check for use before declaration to ensure strict SSA.
          // NOTE: This doesn't check across closures, as that is mostly a runtime determination (see symbol-js/examples/let.js), but we don't care as those are foreign vars and don't affect strict SSA (i.e. correctness).
          self
            .use_before_decl
            .insert(symbol, (name.clone(), Loc(start, end)));
        }
      }
    };
  }

  pub fn enter_class_or_func_name_node(&mut self, node: &mut Node<ClassOrFuncName>) {
    let scope = node.assoc.get::<Scope>().unwrap();
    // It won't exist if it's a global declaration.
    // TODO Is this the only time it won't exist (i.e. is it always safe to ignore None)?
    if let Some(symbol) = scope.find_symbol(node.stx.name.clone()) {
      self.declared.insert(symbol);
    };
  }

  pub fn enter_id_pat_node(&mut self, node: &mut Node<IdPat>) {
    // An identifier pattern doesn't always mean declaration e.g. simple assignment.
    let scope = node.assoc.get::<Scope>().unwrap();
    if *self.in_pat_decl_stack.last().unwrap_or(&false) {
      // It won't exist if it's a global declaration.
      // TODO Is this the only time it won't exist (i.e. is it always safe to ignore None)?
      if let Some(symbol) = scope.find_symbol(node.stx.name.clone()) {
        self.declared.insert(symbol);
      };
      return;
    };

    let name = &node.stx.name;
    let usage_scope = scope;
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
          let start = node.loc.0.saturating_sub(name.len());
          let end = start + name.len();
          // Check for use before declaration to ensure strict SSA.
          // NOTE: This doesn't check across closures, as that is mostly a runtime determination (see symbol-js/examples/let.js), but we don't care as those are foreign vars and don't affect strict SSA (i.e. correctness).
          self
            .use_before_decl
            .insert(symbol, (name.clone(), Loc(start, end)));
        }
      }
    };
  }
}

#[derive(Default)]
pub struct VarAnalysis {
  pub declared: HashSet<Symbol>,
  pub foreign: HashSet<Symbol>,
  pub unknown: HashSet<String>,
  pub use_before_decl: HashMap<Symbol, (String, Loc)>,
}

impl VarAnalysis {
  pub fn analyze(top_level_node: &mut Node<TopLevel>) -> Self {
    let mut var_visitor = VarVisitor::default();
    top_level_node.drive_mut(&mut var_visitor);
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
  use super::VarVisitor;
  use ahash::HashMap;
  use ahash::HashMapExt;
  use ahash::HashSet;
  use derive_visitor::DriveMut;
  use parse_js::parse;
  use symbol_js::compute_symbols;
  use symbol_js::symbol::Scope;
  use symbol_js::symbol::ScopeType;
  use symbol_js::symbol::Symbol;
  use symbol_js::TopLevelMode;

  fn parse_and_visit(source: &str) -> (Scope, VarVisitor) {
    let mut parsed = parse(source).unwrap();
    let top_level_scope = compute_symbols(&mut parsed, TopLevelMode::Global);
    let mut var_visitor = VarVisitor::default();
    parsed.drive_mut(&mut var_visitor);
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
      r#"
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
      HashSet::from_iter([syms["a"], syms["b1"], syms["b2"], syms["c"], syms["d"], syms["e"],]),
    );

    assert_eq!(
      v.foreign,
      HashSet::from_iter([syms["a"], syms["b1"], syms["c"],]),
    );

    assert_eq!(
      v.use_before_decl.keys().cloned().collect::<HashSet<_>>(),
      HashSet::from_iter([]),
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
    let source = r#"
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
      HashSet::from_iter([syms["a"], syms["b1"], syms["b2"], syms["c"], syms["d"],]),
    );

    assert_eq!(v.foreign, HashSet::from_iter([]),);

    assert_eq!(
      v.use_before_decl.keys().cloned().collect::<HashSet<_>>(),
      HashSet::from_iter([syms["a"], syms["b1"], syms["b2"], syms["c"],]),
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

  #[test]
  fn test_var_visitor_function_params() {
    let (s, v) = parse_and_visit(
      r#"
        (() => {
          function f(x, { y }) {
            x;
            y;
          }
          w;
        })();
      "#,
    );

    let mut syms = HashMap::new();
    #[rustfmt::skip]
    test_scope_tree(&mut syms, &s, &T {
      typ: ScopeType::Global,
      syms: vec![],
      children: vec![
        T {
          typ: ScopeType::ArrowFunction,
          syms: vec![("f", "f")],
          children: vec![
            T {
              typ: ScopeType::NonArrowFunction,
              syms: vec![("x", "x"), ("y", "y")],
              children: vec![],
            },
          ],
        },
      ],
    });

    assert_eq!(
      v.declared,
      HashSet::from_iter([syms["f"], syms["x"], syms["y"],]),
    );

    assert_eq!(v.foreign, HashSet::default());
    assert!(v.use_before_decl.is_empty());
    assert_eq!(v.unknown, HashSet::from_iter(["w".to_string()]));
  }
}
