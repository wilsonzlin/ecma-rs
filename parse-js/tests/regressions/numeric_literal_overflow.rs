use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::num::JsNumber;
use parse_js::parse;

#[test]
fn large_hex_literal_keeps_correct_value() {
  let parsed = parse("0x1_0000_0000_0000_0000").unwrap();
  let stmt = parsed.stx.body.first().expect("expected a statement");
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::LitNum(num) => {
        assert_eq!(num.stx.value, JsNumber(18_446_744_073_709_551_616.0));
      }
      other => panic!("expected numeric literal, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  }
}
