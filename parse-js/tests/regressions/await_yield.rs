use parse_js::ast::expr::Expr;
use parse_js::ast::func::FuncBody;
use parse_js::ast::stmt::Stmt;
use parse_js::error::SyntaxErrorType;
use parse_js::operator::OperatorName;
use parse_js::token::TT;
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
  let parsed = parse_with_options(source, js_module_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 1);

  let Stmt::FunctionDecl(func_decl) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  let Some(FuncBody::Block(body)) = &func_decl.stx.function.stx.body else {
    panic!("expected function body");
  };
  assert_eq!(body.len(), 1, "await must not be split by ASI across a newline");

  let Stmt::Expr(stmt) = body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::Unary(unary) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected await unary expression");
  };
  assert_eq!(unary.stx.operator, OperatorName::Await);
}

#[test]
fn await_allows_operand_after_line_terminator_in_comment() {
  let source = "async function f(){ await/*\n*/foo(); }";
  let parsed = parse_with_options(source, js_module_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 1);

  let Stmt::FunctionDecl(func_decl) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  let Some(FuncBody::Block(body)) = &func_decl.stx.function.stx.body else {
    panic!("expected function body");
  };
  assert_eq!(
    body.len(),
    1,
    "await must not be split by ASI across a newline in a comment"
  );

  let Stmt::Expr(stmt) = body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::Unary(unary) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected await unary expression");
  };
  assert_eq!(unary.stx.operator, OperatorName::Await);
}

#[test]
fn await_allows_operand_after_line_terminator_in_single_line_comment() {
  let source = "async function f(){ await//\nfoo(); }";
  let parsed = parse_with_options(source, js_module_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 1);

  let Stmt::FunctionDecl(func_decl) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  let Some(FuncBody::Block(body)) = &func_decl.stx.function.stx.body else {
    panic!("expected function body");
  };
  assert_eq!(
    body.len(),
    1,
    "await must not be split by ASI across a newline in a single-line comment"
  );

  let Stmt::Expr(stmt) = body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::Unary(unary) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected await unary expression");
  };
  assert_eq!(unary.stx.operator, OperatorName::Await);
}

#[test]
fn top_level_await_allows_operand_after_line_terminator() {
  let source = "await\nfoo()";
  let parsed = parse_with_options(source, js_module_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 1);

  let Stmt::Expr(stmt) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::Unary(unary) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected await unary expression");
  };
  assert_eq!(unary.stx.operator, OperatorName::Await);
}

#[test]
fn await_requires_operand() {
  let source = "async function f(){ await; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("expression operand")
  );
  assert_eq!(err.actual_token, Some(TT::Semicolon));
}

#[test]
fn yield_delegated_requires_operand() {
  let source = "function* g(){ yield*; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("expression operand")
  );
  assert_eq!(err.actual_token, Some(TT::Semicolon));
}

#[test]
fn yield_delegated_disallows_line_terminator_before_asterisk() {
  let source = "function* g(){ yield\n* foo; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorAfterYield);
  assert_eq!(err.actual_token, Some(TT::Asterisk));
}

#[test]
fn yield_delegated_disallows_line_terminator_in_comment_before_asterisk() {
  let source = "function* g(){ yield/*\n*/ * foo; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorAfterYield);
  assert_eq!(err.actual_token, Some(TT::Asterisk));
}

#[test]
fn yield_delegated_disallows_line_terminator_in_single_line_comment_before_asterisk() {
  let source = "function* g(){ yield//\n* foo; }";
  let err = parse_with_options(source, js_module_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::LineTerminatorAfterYield);
  assert_eq!(err.actual_token, Some(TT::Asterisk));
}

#[test]
fn yield_delegated_allows_line_terminator_after_asterisk() {
  let source = "function* g(){ yield*\nfoo; }";
  let parsed = parse_with_options(source, js_module_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 1);

  let Stmt::FunctionDecl(func_decl) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  let Some(FuncBody::Block(body)) = &func_decl.stx.function.stx.body else {
    panic!("expected function body");
  };
  assert_eq!(body.len(), 1);

  let Stmt::Expr(stmt) = body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::Unary(unary) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected yield* unary expression");
  };
  assert_eq!(unary.stx.operator, OperatorName::YieldDelegated);

  let Expr::Id(id) = unary.stx.argument.stx.as_ref() else {
    panic!("expected yield* operand to be identifier");
  };
  assert_eq!(id.stx.name, "foo");
}
