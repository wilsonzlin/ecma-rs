use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::num::JsNumber;
use parse_js::parse;
use parse_js::parse::expr::lit::normalise_literal_number;

fn parse_number_value(src: &str) -> JsNumber {
  let parsed = parse(src).unwrap();
  let stmt = parsed.stx.body.first().expect("expected a statement");
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::LitNum(num) => num.stx.value,
      other => panic!("expected numeric literal, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  }
}

#[test]
fn parses_max_finite_literal() {
  let value = parse_number_value("1.7976931348623157e308");
  assert_eq!(value.0, f64::MAX);
}

#[test]
fn overflows_to_infinity() {
  let value = parse_number_value("1e400");
  assert!(value.0.is_infinite() && value.0.is_sign_positive());
}

#[test]
fn parses_min_subnormal() {
  let value = parse_number_value("5e-324");
  assert_eq!(value.0.to_bits(), f64::from_bits(1).to_bits());
}

#[test]
fn parses_legacy_octal_literal() {
  let value = parse_number_value("0777");
  assert_eq!(value.0, 0o777 as f64);
}

#[test]
fn numeric_separators_do_not_change_value() {
  let with_separators = parse_number_value("1_234.5_6e7_8");
  let without_separators = parse_number_value("1234.56e78");
  assert_eq!(with_separators.0.to_bits(), without_separators.0.to_bits());
}

#[test]
fn rejects_hex_floats() {
  assert!(normalise_literal_number("0x1.fp3").is_none());
}
