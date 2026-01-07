use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

#[test]
fn async_function_decl_line_terminator_splits_statements() {
  let ast = parse_with_options("async\nfunction f() {}", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 2);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }

  match ast.stx.body[1].stx.as_ref() {
    Stmt::FunctionDecl(decl) => {
      assert_eq!(decl.stx.name.as_ref().unwrap().stx.name, "f");
      assert!(!decl.stx.function.stx.async_);
    }
    other => panic!("expected function declaration, got {other:?}"),
  }
}

#[test]
fn async_function_decl_without_line_terminator_is_async() {
  let ast = parse_with_options("async function f() {}", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::FunctionDecl(decl) => {
      assert_eq!(decl.stx.name.as_ref().unwrap().stx.name, "f");
      assert!(decl.stx.function.stx.async_);
    }
    other => panic!("expected function declaration, got {other:?}"),
  }
}
