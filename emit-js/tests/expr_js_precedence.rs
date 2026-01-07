use emit_js::{emit_expr_js, EmitOptions, Emitter, ExprCtx};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;

mod util;

fn parse_expr(source: &str) -> Node<Expr> {
  let parsed = parse_js::parse(source).unwrap_or_else(|err| panic!("parse failed for {source:?}: {err:?}"));
  let TopLevel { mut body } = *parsed.stx;
  assert_eq!(body.len(), 1, "expected a single statement for {source:?}");
  match *body.pop().unwrap().stx {
    Stmt::Expr(expr_stmt) => expr_stmt.stx.expr,
    other => panic!("unexpected statement for {source:?}: {other:?}"),
  }
}

fn emit_expr_to_string(expr: &Node<Expr>) -> String {
  let mut emitter = Emitter::new(EmitOptions::minified());
  emit_expr_js(&mut emitter, expr, ExprCtx::Default).expect("emit should succeed");
  String::from_utf8(emitter.into_bytes()).expect("emitter output is UTF-8")
}

fn assert_roundtrip(source: &str, expected_emitted: &str) {
  let expr = parse_expr(source);
  let emitted = emit_expr_to_string(&expr);
  assert_eq!(emitted, expected_emitted, "unexpected emission for {source:?}");

  let emitted_again = emit_expr_to_string(&expr);
  assert_eq!(
    emitted_again, emitted,
    "emission is not deterministic for {source:?}"
  );

  let reparsed = parse_expr(&emitted);
  assert_eq!(
    util::serialize_without_locs(&expr),
    util::serialize_without_locs(&reparsed),
    "roundtrip mismatch for {source:?} emitted as {emitted:?}"
  );
}

#[test]
fn expr_js_precedence_regressions() {
  assert_roundtrip("(a ** b) ** c", "(a**b)**c");
  assert_roundtrip("(a = b) = c", "(a=b)=c");
  assert_roundtrip("(a ? b : c) ? d : e", "(a?b:c)?d:e");
  assert_roundtrip("a ?? (b && c)", "a??(b&&c)");
  assert_roundtrip("(a && b) ?? c", "(a&&b)??c");
  assert_roundtrip("(a ?? b) || c", "(a??b)||c");
  assert_roundtrip("(-a) ** b", "(-a)**b");
}

