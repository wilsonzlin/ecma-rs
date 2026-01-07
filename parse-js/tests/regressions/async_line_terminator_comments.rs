use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::parse_with_options;
use parse_js::{Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

#[test]
fn async_comment_with_newline_does_not_form_async_function() {
  let parsed = parse_with_options("async/*\n*/function f(){}", ecma_script_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }
  assert!(matches!(
    parsed.stx.body[1].stx.as_ref(),
    Stmt::FunctionDecl(_)
  ));
}

#[test]
fn async_comment_without_newline_forms_async_function() {
  let parsed = parse_with_options("async/*ok*/function f(){}", ecma_script_opts()).unwrap();
  assert_eq!(parsed.stx.body.len(), 1);
  let Stmt::FunctionDecl(decl) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  assert!(decl.stx.function.stx.async_);
}
