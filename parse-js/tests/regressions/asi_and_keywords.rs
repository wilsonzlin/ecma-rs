use parse_js::ast::stmt::Stmt;
use parse_js::error::SyntaxErrorType;
use parse_js::parse_with_options;
use parse_js::{Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

#[test]
fn asi_splits_identifiers_only_across_line_terminators() {
  let parsed = parse_with_options("a\nb", ecma_script_opts()).expect("expected ASI split");
  assert_eq!(parsed.stx.body.len(), 2);
  assert!(matches!(parsed.stx.body[0].stx.as_ref(), Stmt::Expr(_)));
  assert!(matches!(parsed.stx.body[1].stx.as_ref(), Stmt::Expr(_)));

  assert!(parse_with_options("a b", ecma_script_opts()).is_err());
}

#[test]
fn asi_does_not_split_before_brace_without_line_terminator() {
  assert!(parse_with_options("a {}", ecma_script_opts()).is_err());
}

#[test]
fn await_allows_line_terminator_before_operand() {
  assert!(parse_with_options(
    "async function f(){ await\nfoo(); }",
    ecma_script_opts()
  )
  .is_ok());
}

#[test]
fn await_requires_operand() {
  assert!(
    parse_with_options("async function f(){ await; }", ecma_script_opts()).is_err(),
    "await must not accept a missing operand"
  );
}

#[test]
fn yield_star_disallows_line_terminator_between_yield_and_star() {
  let err =
    parse_with_options("function* g(){ yield\n* other; }", ecma_script_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorAfterYield);
}
