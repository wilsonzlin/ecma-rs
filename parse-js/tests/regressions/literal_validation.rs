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
fn string_allows_unescaped_line_separator_codepoints() {
  let source = format!("'hello{}world'", '\u{2028}');
  parse(&source).unwrap();
  let source = format!("'hello{}world'", '\u{2029}');
  parse(&source).unwrap();
}

#[test]
fn string_allows_surrogate_escapes() {
  // Rust `String` cannot represent surrogate code points directly; the parser
  // maps them to U+FFFD while still accepting the literal.
  parse("\"\\u{D800}\"").unwrap();
  parse("\"\\uD800\"").unwrap();
  // Surrogate pair should decode into a valid scalar.
  parse("\"\\uD83D\\uDE00\"").unwrap();
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
