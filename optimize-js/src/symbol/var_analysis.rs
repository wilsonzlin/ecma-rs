use crate::symbol::semantics::{
  assoc_declared_symbol, assoc_resolved_symbol_info, assoc_scope_id, JsSymbols, ScopeId, ScopeKind,
  SymbolId,
};
use ahash::HashMap;
use ahash::HashSet;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::ClassOrFuncName;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::WithStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

type IdExprNode = Node<IdExpr>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type IdPatNode = Node<IdPat>;
type WithStmtNode = Node<WithStmt>;

// Four tasks (fill out each field as appropriate).
#[derive(Debug, VisitorMut)]
#[visitor(
  IdExprNode(enter),
  ClassOrFuncNameNode(enter),
  IdPatNode(enter),
  WithStmtNode(enter)
)]
struct VarVisitor<'a> {
  symbols: &'a JsSymbols,
  declared: HashSet<SymbolId>,
  foreign: HashSet<SymbolId>,
  unknown: HashSet<String>,
  use_before_decl: HashMap<SymbolId, (String, Loc)>,
  dynamic_scope: Option<Loc>,
}

// The lifted scope is the nearest self-or-ancestor scope that is not a block, or the self-or-ancestor scope just below the global scope.
// This is useful as we don't want a usage in an inner block to count as "foreign".
fn lifted_scope(symbols: &JsSymbols, scope: ScopeId) -> ScopeId {
  if symbols.scope_kind(scope) != ScopeKind::Block {
    return scope;
  }
  let Some(parent) = symbols.parent_scope(scope) else {
    return scope;
  };
  if symbols.scope_kind(parent) == ScopeKind::Global {
    return scope;
  }
  lifted_scope(symbols, parent)
}

impl<'a> VarVisitor<'a> {
  fn mark_declared(&mut self, symbol: SymbolId) {
    self.declared.insert(symbol);
  }

  fn note_use(&mut self, name: &str, assoc: &NodeAssocData, loc: Loc) {
    let Some(usage_scope) = assoc_scope_id(assoc) else {
      self.unknown.insert(name.to_string());
      return;
    };
    let Some(resolved) = assoc_resolved_symbol_info(assoc) else {
      self.unknown.insert(name.to_string());
      return;
    };
    let Some(symbol) = resolved.symbol else {
      self.unknown.insert(name.to_string());
      return;
    };
    let usage_ls = lifted_scope(&self.symbols, usage_scope);
    let decl_scope = self.symbols.symbol_decl_scope(symbol);
    let decl_ls = lifted_scope(&self.symbols, decl_scope);
    if usage_ls != decl_ls {
      self.foreign.insert(symbol);
    }
    if resolved.in_tdz {
      self
        .use_before_decl
        .entry(symbol)
        .or_insert_with(|| (name.to_string(), loc));
    }
  }

  pub fn enter_id_expr_node(&mut self, node: &mut Node<IdExpr>) {
    self.note_use(&node.stx.name, &node.assoc, node.loc);
  }

  pub fn enter_class_or_func_name_node(&mut self, node: &mut Node<ClassOrFuncName>) {
    if let Some(symbol) = assoc_declared_symbol(&node.assoc) {
      self.mark_declared(symbol);
    };
  }

  pub fn enter_id_pat_node(&mut self, node: &mut Node<IdPat>) {
    if let Some(symbol) = assoc_declared_symbol(&node.assoc) {
      self.mark_declared(symbol);
    } else {
      self.note_use(&node.stx.name, &node.assoc, node.loc);
    }
  }

  pub fn enter_with_stmt_node(&mut self, node: &mut WithStmtNode) {
    self.dynamic_scope.get_or_insert(node.loc);
  }
}

#[derive(Default)]
pub struct VarAnalysis {
  pub declared: HashSet<SymbolId>,
  pub foreign: HashSet<SymbolId>,
  pub unknown: HashSet<String>,
  pub use_before_decl: HashMap<SymbolId, (String, Loc)>,
  pub dynamic_scope: Option<Loc>,
}

impl VarAnalysis {
  pub fn analyze(top_level_node: &mut Node<TopLevel>, symbols: &JsSymbols) -> Self {
    let mut var_visitor = VarVisitor {
      symbols,
      declared: HashSet::default(),
      foreign: HashSet::default(),
      unknown: HashSet::default(),
      use_before_decl: HashMap::default(),
      dynamic_scope: None,
    };
    top_level_node.drive_mut(&mut var_visitor);
    Self {
      declared: var_visitor.declared,
      foreign: var_visitor.foreign,
      unknown: var_visitor.unknown,
      use_before_decl: var_visitor.use_before_decl,
      dynamic_scope: var_visitor.dynamic_scope,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::VarAnalysis;
  use ahash::HashMap;
  use ahash::HashSet;
  use diagnostics::FileId;
  use parse_js::parse;
  use semantic_js::js::TopLevelMode;

  use crate::symbol::semantics::{JsSymbols, ScopeId, ScopeKind, SymbolId};

  fn parse_and_visit_with_mode(source: &str, mode: TopLevelMode) -> (VarAnalysis, JsSymbols) {
    let mut parsed = parse(source).unwrap();
    let (symbols, _diagnostics) = JsSymbols::bind(&mut parsed, mode, FileId(0));
    let analysis = VarAnalysis::analyze(&mut parsed, &symbols);
    (analysis, symbols)
  }

  fn parse_and_visit(source: &str) -> (VarAnalysis, JsSymbols) {
    parse_and_visit_with_mode(source, TopLevelMode::Global)
  }

  struct T {
    typ: ScopeKind,
    syms: Vec<(&'static str, &'static str)>, // (name, key)
    children: Vec<T>,
  }

  fn collect_scope_tree(
    out: &mut HashMap<&'static str, SymbolId>,
    symbols: &JsSymbols,
    scope: ScopeId,
    m: &T,
  ) {
    assert_eq!(symbols.scope_kind(scope), m.typ);
    let mut in_scope = symbols.symbols_in_scope(scope);
    in_scope.sort_by(|a, b| a.1.cmp(&b.1));
    assert_eq!(in_scope.len(), m.syms.len());
    for ((sym, name), (expected_name, key)) in in_scope.into_iter().zip(m.syms.iter()) {
      assert_eq!(&name, expected_name);
      assert!(out.insert(key, sym).is_none());
    }
    let mut children: Vec<_> = symbols.children(scope).collect();
    children.sort_by_key(|s| s.raw_id());
    assert_eq!(children.len(), m.children.len());
    for (i, child) in children.into_iter().enumerate() {
      collect_scope_tree(out, symbols, child, &m.children[i]);
    }
  }

  #[test]
  fn test_var_visitor() {
    let (v, symbols) = parse_and_visit(
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

    let mut syms = HashMap::default();
    #[rustfmt::skip]
    collect_scope_tree(&mut syms, &symbols, symbols.top_scope(), &T {
      typ: ScopeKind::Global,
      syms: vec![],
      children: vec![
        T {
          typ: ScopeKind::ArrowFunction,
          syms: vec![("a", "a"), ("b", "b1")],
          children: vec![
            T {
              typ: ScopeKind::ArrowFunction,
              syms: vec![("c", "c")],
              children: vec![
                T {
                  typ: ScopeKind::ArrowFunction,
                  syms: vec![("b", "b2")],
                  children: vec![
                    T {
                      typ: ScopeKind::Block,
                      syms: vec![("d", "d")],
                      children: vec![
                        T {
                          typ: ScopeKind::Block,
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
    let (v, symbols) = parse_and_visit(source);

    let mut syms = HashMap::default();
    #[rustfmt::skip]
    collect_scope_tree(&mut syms, &symbols, symbols.top_scope(), &T {
      typ: ScopeKind::Global,
      syms: vec![],
      children: vec![
        T {
          typ: ScopeKind::Block,
          syms: vec![("a", "a")],
          children: vec![
            T {
              typ: ScopeKind::Block,
              syms: vec![("b", "b1"), ("c", "c")],
              children: vec![
                T {
                  typ: ScopeKind::Block,
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
    let (v, symbols) = parse_and_visit(
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

    let mut syms = HashMap::default();
    #[rustfmt::skip]
    collect_scope_tree(&mut syms, &symbols, symbols.top_scope(), &T {
      typ: ScopeKind::Global,
      syms: vec![],
      children: vec![
        T {
          typ: ScopeKind::ArrowFunction,
          syms: vec![("f", "f")],
          children: vec![
            T {
              typ: ScopeKind::NonArrowFunction,
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

  #[test]
  fn hoisted_var_and_function_are_not_reported() {
    let (analysis, _symbols) = parse_and_visit_with_mode(
      "var x; f(); function f() { return x; }",
      TopLevelMode::Module,
    );
    assert!(
      analysis.use_before_decl.is_empty(),
      "hoisted bindings should not count as use-before-declaration"
    );
  }

  #[test]
  fn var_use_before_declaration_is_allowed() {
    let (analysis, _symbols) =
      parse_and_visit_with_mode("console.log(x); var x = 1;", TopLevelMode::Module);
    assert!(
      analysis.use_before_decl.is_empty(),
      "var should be hoisted and initialized to undefined"
    );
  }

  #[test]
  fn let_use_before_declaration_is_reported() {
    let (analysis, symbols) =
      parse_and_visit_with_mode("console.log(x); let x = 1;", TopLevelMode::Module);
    let top_scope = symbols.top_scope();
    let symbol_x = symbols
      .symbols_in_scope(top_scope)
      .into_iter()
      .find(|(_, name)| name == "x")
      .map(|(sym, _)| sym)
      .expect("let binding for x");
    assert!(analysis.use_before_decl.contains_key(&symbol_x));
  }
}
