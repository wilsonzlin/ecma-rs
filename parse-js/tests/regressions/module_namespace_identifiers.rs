use parse_js::error::SyntaxErrorType;
use parse_js::token::TT;
use parse_js::parse;

#[test]
fn import_named_specifier_disallows_string_literal_alias() {
  let err = parse(r#"import { foo as "bar" } from "mod";"#).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("identifier"));
  assert_eq!(err.actual_token, Some(TT::LiteralString));
}

#[test]
fn import_star_disallows_string_literal_alias() {
  let err = parse(r#"import * as "ns" from "mod";"#).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("identifier"));
  assert_eq!(err.actual_token, Some(TT::LiteralString));
}

#[test]
fn import_string_name_requires_as_clause() {
  let err = parse(r#"import { "a-b" } from "mod";"#).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("identifier"));
  assert_eq!(err.actual_token, Some(TT::LiteralString));
}

#[test]
fn export_list_disallows_string_literal_exportable_without_from() {
  let err = parse(r#"export { "a-b" as foo };"#).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("identifier"));
}
