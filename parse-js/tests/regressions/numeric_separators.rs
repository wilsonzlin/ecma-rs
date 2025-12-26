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
