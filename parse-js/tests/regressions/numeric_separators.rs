use parse_js::error::SyntaxErrorType;
use parse_js::parse;

#[test]
fn double_underscore_in_integer_is_invalid() {
  let err = parse("1__0").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
}

#[test]
fn underscore_cannot_split_exponent_marker() {
  let err = parse("1.0e_+10").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
}

#[test]
fn numeric_separators_are_disallowed_after_leading_zero() {
  let err = parse("0_0").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
  let err = parse("08_1").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
  let err = parse("0_0.1").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
}

#[test]
fn legacy_octal_literals_cannot_have_fractional_or_exponent_parts() {
  let err = parse("010e1").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
  let err = parse("010.1").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::MalformedLiteralNumber);
}
