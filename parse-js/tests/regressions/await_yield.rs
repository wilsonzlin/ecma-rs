use parse_js::error::SyntaxErrorType;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_module_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Module,
  }
}

#[test]
fn await_allows_operand_after_line_terminator_in_async_function() {
  let source = "async function f(){ await\nfoo(); }";
  parse_with_options(source, js_module_opts()).unwrap();
}

#[test]
fn top_level_await_allows_operand_after_line_terminator() {
  let source = "await\nfoo()";
  parse_with_options(source, js_module_opts()).unwrap();
}

#[test]
fn await_requires_operand() {
  let source = "async function f(){ await; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("expression operand")
  );
}

#[test]
fn yield_delegated_requires_operand() {
  let source = "function* g(){ yield*; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("expression operand")
  );
}

#[test]
fn yield_delegated_disallows_line_terminator_before_asterisk() {
  let source = "function* g(){ yield\n* foo; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorAfterYield);
}
