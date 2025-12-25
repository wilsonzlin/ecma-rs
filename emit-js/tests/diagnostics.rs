use diagnostics::FileId;
use emit_js::{emit_top_level_diagnostic, EmitOptions};
use parse_js::ast::expr::{Expr, IdExpr, TypeAssertionExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{ExprStmt, Stmt};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

#[test]
fn reports_unsupported_statement_as_diagnostic() {
  let assertion = TypeAssertionExpr {
    expression: Box::new(Node::new(
      Loc(0, 1),
      Expr::Id(Node::new(Loc(0, 1), IdExpr { name: "x".into() })),
    )),
    type_annotation: None,
    const_assertion: false,
  };
  let expr = Node::new(
    Loc(0, 1),
    Expr::TypeAssertion(Node::new(Loc(0, 1), assertion)),
  );
  let stmt = Node::new(
    Loc(0, 1),
    Stmt::Expr(Node::new(Loc(0, 1), ExprStmt { expr })),
  );
  let ast = Node::new(Loc(0, 1), TopLevel { body: vec![stmt] });
  let diagnostic = emit_top_level_diagnostic(FileId(0), &ast, EmitOptions::default())
    .expect_err("emission should fail for unsupported statements");

  assert!(diagnostic.code.as_str().starts_with("EMIT"));
  assert_eq!(diagnostic.code.as_str(), "EMIT0002");
  assert!(
    diagnostic.primary.range.len() > 0,
    "primary span should be non-empty"
  );
}
