use crate::symbol::Scope;
use crate::symbol::ScopeType;
use crate::symbol::Symbol;
use ahash::HashMap;
use ahash::HashSet;
use derive_visitor::Drive;
use derive_visitor::Visitor;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::PatDecl;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

type PatDeclNode = Node<PatDecl>;
type IdExprNode = Node<IdExpr>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type IdPatNode = Node<IdPat>;

// Four tasks (fill out each field as appropriate).
#[derive(Debug, Default, Visitor)]
#[visitor(
  PatDeclNode,
  IdExprNode(enter),
  ClassOrFuncNameNode(enter),
  IdPatNode(enter)
)]
struct VarVisitor {
  pub declared: HashSet<Symbol>,
  pub foreign: HashSet<Symbol>,
  pub unknown: HashSet<String>,
  pub use_before_decl: HashMap<Symbol, Loc>,

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
  pub fn enter_pat_decl_node(&mut self, _node: &Node<PatDecl>) {
    self.in_pat_decl_stack.push(true);
  }

  pub fn exit_pat_decl_node(&mut self, _node: &Node<PatDecl>) {
    self.in_pat_decl_stack.pop();
  }

  pub fn enter_id_expr_node(&mut self, node: &Node<IdExpr>) {
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
          // Check for use before declaration to ensure strict SSA.
          // NOTE: This doesn't check across closures, as that is mostly a runtime determination (see symbol-js/examples/let.js), but we don't care as those are foreign vars and don't affect strict SSA (i.e. correctness).
          self.use_before_decl.insert(symbol, node.loc);
        }
      }
    };
  }

  pub fn enter_class_or_func_name_node(&mut self, node: &Node<ClassOrFuncName>) {
    let scope = node.assoc.get::<Scope>().unwrap();
    // It won't exist if it's a global declaration.
    // TODO Is this the only time it won't exist (i.e. is it always safe to ignore None)?
    if let Some(symbol) = scope.find_symbol(node.stx.name.clone()) {
      assert!(self.declared.insert(symbol));
    };
  }

  pub fn enter_id_pat_node(&mut self, node: &Node<IdPat>) {
    // An identifier pattern doesn't always mean declaration e.g. simple assignment.
    if *self.in_pat_decl_stack.last().unwrap_or(&false) {
      let scope = node.assoc.get::<Scope>().unwrap();
      // It won't exist if it's a global declaration.
      // TODO Is this the only time it won't exist (i.e. is it always safe to ignore None)?
      if let Some(symbol) = scope.find_symbol(node.stx.name.clone()) {
        assert!(self.declared.insert(symbol));
      };
    };
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
  pub fn analyze(top_level_node: &Node<TopLevel>) -> Self {
    let mut var_visitor = VarVisitor::default();
    top_level_node.drive(&mut var_visitor);
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
  use crate::compute_symbols;
  use crate::symbol::Scope;
  use crate::symbol::ScopeType;
  use crate::symbol::Symbol;
  use crate::TopLevelMode;
  use ahash::HashMap;
  use ahash::HashMapExt;
  use ahash::HashSet;
  use derive_visitor::Drive;
  use parse_js::parse;

  fn parse_and_visit(source: &str) -> (Scope, VarVisitor) {
    let mut parsed = parse(source).unwrap();
    let top_level_scope = compute_symbols(&mut parsed, TopLevelMode::Global);
    let mut var_visitor = VarVisitor::default();
    parsed.drive(&mut var_visitor);
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
    let mut map = HashMap::new();
    test_scope_tree(
      &mut map,
      &s,
      &T {
        typ: ScopeType::Global,
        syms: vec![("z", "z"), ("x", "x"), ("w", "w")],
        children: vec![T {
          typ: ScopeType::ArrowFunction,
          syms: vec![("a", "a"), ("b", "b")],
          children: vec![T {
            typ: ScopeType::ArrowFunction,
            syms: vec![("c", "c")],
            children: vec![T {
              typ: ScopeType::ArrowFunction,
              syms: vec![("b", "b1")],
              children: vec![T {
                typ: ScopeType::Block,
                syms: vec![("d", "d")],
                children: vec![T {
                  typ: ScopeType::Block,
                  syms: vec![("e", "e")],
                  children: vec![],
                }],
              }],
            }],
          }],
        }],
      },
    );
    assert_eq!(map.len(), 8);

    // Verify foreign/unknown/use-before-decl.
    let mut expected_foreign = HashSet::new();
    let mut expected_unknown = HashSet::new();
    expected_unknown.insert("y".to_string());
    expected_unknown.insert("z".to_string());
    expected_unknown.insert("w".to_string());
    let mut use_before_decl = HashMap::new();
    for sym in ["a", "b"] {
      let sym = map.get(sym).unwrap();
      assert!(expected_foreign.insert(*sym));
    }
    for sym in ["y", "z", "w"] {
      use_before_decl.insert(*map.get(sym).unwrap(), Default::default());
    }

    assert_eq!(v.foreign, expected_foreign);
    assert_eq!(v.unknown, expected_unknown);
    assert_eq!(
      v.use_before_decl.keys().collect::<Vec<_>>(),
      use_before_decl.keys().collect::<Vec<_>>()
    );
  }
}
