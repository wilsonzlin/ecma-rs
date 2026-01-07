use parse_js::ast::stmt::Stmt;
use parse_js::error::SyntaxErrorType;
use parse_js::operator::OperatorName;
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
  assert!(parse_with_options("async function f(){ await\nfoo(); }", ecma_script_opts()).is_ok());
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
  let err = parse_with_options("function* g(){ yield\n* other; }", ecma_script_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorAfterYield);
}

#[test]
fn yield_is_restricted_production_across_line_terminators() {
  let parsed = parse_with_options(
    "function* g(){ const x = yield\n+1; return x; }",
    ecma_script_opts(),
  )
  .unwrap();

  let Stmt::FunctionDecl(func_decl) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  let Some(parse_js::ast::func::FuncBody::Block(body)) = &func_decl.stx.function.stx.body else {
    panic!("expected function body");
  };

  assert_eq!(body.len(), 3);
  assert!(matches!(body[0].stx.as_ref(), Stmt::VarDecl(_)));
  assert!(matches!(body[1].stx.as_ref(), Stmt::Expr(_)));
  assert!(matches!(body[2].stx.as_ref(), Stmt::Return(_)));

  let Stmt::VarDecl(var_decl) = body[0].stx.as_ref() else {
    unreachable!();
  };
  let init = var_decl.stx.declarators[0]
    .initializer
    .as_ref()
    .expect("initializer missing");
  match init.stx.as_ref() {
    parse_js::ast::expr::Expr::Unary(unary) => assert_eq!(unary.stx.operator, OperatorName::Yield),
    other => panic!("expected yield initializer, got {other:?}"),
  }
}

#[test]
fn yield_requires_parentheses_in_higher_precedence_expressions() {
  let err =
    parse_with_options("function* g(){ return 1 + yield 2; }", ecma_script_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("parenthesized expression")
  );

  parse_with_options("function* g(){ return 1 + (yield 2); }", ecma_script_opts()).unwrap();
}

#[test]
fn yield_requires_parentheses_in_conditional_test() {
  let err =
    parse_with_options("function* g(){ return yield ? 1 : 2; }", ecma_script_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("parenthesized expression")
  );

  parse_with_options("function* g(){ return (yield) ? 1 : 2; }", ecma_script_opts()).unwrap();
}

#[test]
fn yield_requires_parentheses_before_exponentiation_operand() {
  let err =
    parse_with_options("function* g(){ return 2 ** yield 1; }", ecma_script_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("parenthesized expression")
  );

  parse_with_options("function* g(){ return 2 ** (yield 1); }", ecma_script_opts()).unwrap();
}

#[test]
fn await_requires_parentheses_before_exponentiation_operand() {
  let err = parse_with_options(
    "async function f(){ return await 2 ** 2; }",
    ecma_script_opts(),
  )
  .unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("parenthesized expression")
  );

  parse_with_options(
    "async function f(){ return await (2 ** 2); }",
    ecma_script_opts(),
  )
  .unwrap();
}
