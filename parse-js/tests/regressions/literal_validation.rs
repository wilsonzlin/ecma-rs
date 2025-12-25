use parse_js::error::SyntaxErrorType;
use parse_js::parse;

#[test]
fn duplicate_regex_flags_are_rejected() {
  let err = parse("/value/gg").unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("valid regex flags")
  );
}

#[test]
fn invalid_string_escape_reports_error() {
  let err = parse("\"\\u{110000}\"").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::InvalidCharacterEscape);
}

#[test]
fn string_with_line_terminator_is_invalid() {
  let err = parse("'line\nbreak'").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorInString);
}

#[test]
fn invalid_template_escape_reports_error() {
  let err = parse("`\\u{110000}`").unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::InvalidCharacterEscape);
}

#[test]
fn tagged_templates_allow_invalid_escapes() {
  assert!(parse("tag`\\u{110000}`").is_ok());
}
