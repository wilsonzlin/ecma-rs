use emit_js::emit_expr;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::parse;

fn parse_bigint_expr(source: &str) -> Node<Expr> {
  let mut parsed = parse(source).expect("source should parse");
  let stmt = parsed.stx.body.pop().expect("expected a statement");
  match *stmt.stx {
    Stmt::Expr(expr_stmt) => {
      let expr = expr_stmt.stx.expr;
      match expr.stx.as_ref() {
        Expr::LitBigInt(_) => expr,
        other => panic!("expected bigint literal, got {:?}", other),
      }
    }
    other => panic!("expected expression statement, got {:?}", other),
  }
}

fn emit(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr(&mut out, expr, &mut emit_type).expect("emit expression");
  out
}

fn assert_roundtrip(source: &str) {
  let expr = parse_bigint_expr(source);
  let expected = match expr.stx.as_ref() {
    Expr::LitBigInt(lit) => format!("{}n", lit.stx.value),
    _ => unreachable!(),
  };
  let emitted = emit(&expr);
  assert_eq!(emitted, expected);
  let reparsed = parse_bigint_expr(&emitted);
  match reparsed.stx.as_ref() {
    Expr::LitBigInt(lit) => assert_eq!(format!("{}n", lit.stx.value), expected),
    other => panic!("expected bigint literal after reparse, got {:?}", other),
  }
}

#[test]
fn bigints_emit_in_normalised_form() {
  assert_roundtrip("0XFF_FFn");
  assert_roundtrip("0B1_010n");
  assert_roundtrip("1_000n");
}
