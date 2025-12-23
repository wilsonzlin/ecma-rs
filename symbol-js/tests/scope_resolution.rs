use derive_visitor::{Drive, Visitor};
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::parse;
use symbol_js::compute_symbols;
use symbol_js::symbol::Scope;
use symbol_js::TopLevelMode;

type IdPatNode = Node<IdPat>;
type IdExprNode = Node<IdExpr>;

#[derive(Default, Visitor)]
#[visitor(IdPatNode(enter), IdExprNode(enter))]
struct ScopeCollector {
  decl_scope: Option<Scope>,
  use_scope: Option<Scope>,
}

impl ScopeCollector {
  pub fn enter_id_pat_node(&mut self, node: &IdPatNode) {
    if node.stx.name == "value" {
      self.decl_scope = Some(node.assoc.get::<Scope>().unwrap().clone());
    }
  }

  pub fn enter_id_expr_node(&mut self, node: &IdExprNode) {
    if node.stx.name == "value" {
      self.use_scope = Some(node.assoc.get::<Scope>().unwrap().clone());
    }
  }
}

#[test]
fn resolves_outer_let_with_declaration_scope() {
  let mut top_level = parse(
    r#"
      function outer() {
        let value = 1;
        return function inner() {
          return value;
        };
      }
    "#,
  )
  .unwrap();

  compute_symbols(&mut top_level, TopLevelMode::Module);

  let mut collector = ScopeCollector::default();
  top_level.drive(&mut collector);

  let decl_scope = collector.decl_scope.expect("declaration scope captured");
  let use_scope = collector.use_scope.expect("usage scope captured");

  assert_ne!(decl_scope, use_scope, "declaration should be in an outer closure");

  let (resolved_scope, symbol) = use_scope
    .find_symbol_up_to_with_scope("value".to_string(), |_| false)
    .expect("symbol should resolve across nested closures");

  assert_eq!(resolved_scope, decl_scope, "should return the declaration scope");

  let decl_symbol = decl_scope
    .find_symbol("value".to_string())
    .expect("declaration scope should contain symbol");
  assert_eq!(symbol, decl_symbol);
}
