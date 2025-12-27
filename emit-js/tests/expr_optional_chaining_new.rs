use emit_js::emit_expr;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::TypeExpr;

mod util;

fn parse_expr(source: &str) -> Node<Expr> {
  let parsed = parse_js::parse(source).expect("parse failed");
  let TopLevel { mut body } = *parsed.stx;
  assert_eq!(body.len(), 1, "expected a single statement");
  match *body.pop().unwrap().stx {
    Stmt::Expr(expr_stmt) => expr_stmt.stx.expr,
    other => panic!("unexpected statement: {other:?}"),
  }
}

fn emit_expr_to_string(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr(&mut out, expr, &mut emit_type).expect("emit should succeed");
  out
}

fn assert_roundtrip(source: &str, expected_emitted: &str) {
  let expr = parse_expr(source);
  let emitted = emit_expr_to_string(&expr);
  assert_eq!(emitted, expected_emitted);

  let reparsed = parse_expr(&emitted);
  assert_eq!(
    util::serialize_without_locs(&expr),
    util::serialize_without_locs(&reparsed),
    "roundtrip mismatch for `{source}` emitted as `{emitted}`"
  );
}

#[test]
fn parenthesizes_new_optional_chain_without_args() {
  assert_roundtrip("new abc?.def", "new (abc?.def)");
}

#[test]
fn parenthesizes_new_optional_chain_with_args() {
  assert_roundtrip("new abc?.def()", "new (abc?.def)()");
}

#[test]
fn parenthesizes_new_optional_chain_with_unary_plus() {
  assert_roundtrip("+new abc?.def();", "+new (abc?.def)()");
}
