use parse_js::error::SyntaxErrorType;
use parse_js::token::TT;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn tsx_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Script,
  }
}

#[test]
fn jsx_text_rejects_unescaped_brace_in_text() {
  let err = parse_with_options("<div>}</div>", tsx_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::RequiredTokenNotFound(TT::ChevronLeftSlash));
  assert_eq!(err.actual_token, Some(TT::BraceClose));
}

#[test]
fn jsx_text_rejects_unescaped_gt_in_text() {
  let err = parse_with_options("<div>></div>", tsx_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::RequiredTokenNotFound(TT::ChevronLeftSlash));
  assert_eq!(err.actual_token, Some(TT::ChevronRight));
}

#[test]
fn jsx_attribute_string_allows_escaped_quote() {
  let source = "<div attr=\"&#0123;&hellip;&#x7D;\\\"></div>;";
  parse_with_options(source, tsx_opts()).unwrap();
}
