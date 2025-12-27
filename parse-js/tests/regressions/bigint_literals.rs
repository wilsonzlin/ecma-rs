use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::error::SyntaxErrorType;
use parse_js::parse;

fn bigint_value(source: &str) -> String {
  let parsed = parse(source).expect("source should parse");
  let stmt = parsed.stx.body.first().expect("expected a statement");
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::LitBigInt(lit) => lit.stx.value.clone(),
      other => panic!("expected bigint literal, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  }
}

#[test]
fn normalises_decimal_bigint() {
  assert_eq!(bigint_value("1_000n"), "1000n");
  assert_eq!(bigint_value("123n"), "123n");
}

#[test]
fn normalises_prefixed_bigints() {
  assert_eq!(bigint_value("0B10_10n"), "0b1010n");
  assert_eq!(bigint_value("0O7_7n"), "0o77n");
  assert_eq!(bigint_value("0XFF_FFn"), "0xffffn");
}

#[test]
fn invalid_digits_are_rejected() {
  let err = parse("0b102n").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralBigInt);
}

#[test]
fn malformed_separators_are_rejected() {
  let err = parse("1__0n").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralBigInt);
}

#[test]
fn leading_zero_decimal_bigint_is_rejected() {
  let err = parse("00n").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralBigInt);
}
