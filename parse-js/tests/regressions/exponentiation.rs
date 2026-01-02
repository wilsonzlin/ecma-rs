use parse_js::error::SyntaxErrorType;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

fn ts_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

#[test]
fn exponentiation_rejects_unparenthesized_unary_lhs() {
  let err = parse_with_options("-1 ** 2;", js_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("parenthesized expression"));
}

#[test]
fn exponentiation_allows_parenthesized_unary_lhs() {
  parse_with_options("(-1) ** 2;", js_opts()).unwrap();
}

#[test]
fn exponentiation_allows_update_expression_lhs() {
  parse_with_options("let x = 1; x++ ** 2;", js_opts()).unwrap();
}

#[test]
fn exponentiation_rejects_type_assertion_lhs_without_parentheses() {
  let err = parse_with_options("<number>temp ** 3;", ts_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("parenthesized expression"));
}

#[test]
fn exponentiation_allows_parenthesized_type_assertion_with_unary_operand() {
  let source = "let temp: any; (<number>--temp) ** 3;";
  parse_with_options(source, ts_opts()).unwrap();
}

#[test]
fn template_literal_allows_empty_tail_after_substitution() {
  parse_with_options("`${1}`;", js_opts()).unwrap();
}

