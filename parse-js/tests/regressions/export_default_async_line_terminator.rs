use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn strict_module_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Module,
  }
}

#[test]
fn export_default_async_line_terminator_treats_async_as_expression() {
  let ast = parse_with_options("export default async\nfunction f() {}", strict_module_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 2);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::ExportDefaultExpr(stmt) => match stmt.stx.expression.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected export default expr statement, got {other:?}"),
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
fn export_default_async_without_line_terminator_is_async_function_decl() {
  let ast = parse_with_options(
    "export default async function f() {}",
    strict_module_opts(),
  )
  .unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::FunctionDecl(decl) => {
      assert!(decl.stx.export);
      assert!(decl.stx.export_default);
      assert!(decl.stx.function.stx.async_);
      assert_eq!(decl.stx.name.as_ref().unwrap().stx.name, "f");
    }
    other => panic!("expected function declaration, got {other:?}"),
  }
}

#[test]
fn export_async_function_requires_no_line_terminator() {
  assert!(parse_with_options("export async\nfunction f() {}", strict_module_opts()).is_err());
}

#[test]
fn export_default_async_comment_with_newline_treats_async_as_expression() {
  let ast = parse_with_options(
    "export default async/*\n*/function f() {}",
    strict_module_opts(),
  )
  .unwrap();
  assert_eq!(ast.stx.body.len(), 2);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::ExportDefaultExpr(stmt) => match stmt.stx.expression.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected export default expr statement, got {other:?}"),
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
fn export_default_async_comment_without_newline_is_async_function_decl() {
  let ast = parse_with_options(
    "export default async/*ok*/function f() {}",
    strict_module_opts(),
  )
  .unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::FunctionDecl(decl) => {
      assert!(decl.stx.export);
      assert!(decl.stx.export_default);
      assert!(decl.stx.function.stx.async_);
      assert_eq!(decl.stx.name.as_ref().unwrap().stx.name, "f");
    }
    other => panic!("expected function declaration, got {other:?}"),
  }
}

#[test]
fn export_async_comment_without_newline_is_async_function_decl() {
  let ast = parse_with_options(
    "export async/*ok*/function f() {}",
    strict_module_opts(),
  )
  .unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::FunctionDecl(decl) => {
      assert!(decl.stx.export);
      assert!(!decl.stx.export_default);
      assert!(decl.stx.function.stx.async_);
      assert_eq!(decl.stx.name.as_ref().unwrap().stx.name, "f");
    }
    other => panic!("expected function declaration, got {other:?}"),
  }
}

#[test]
fn export_async_comment_with_newline_is_rejected() {
  assert!(parse_with_options(
    "export async/*\n*/function f() {}",
    strict_module_opts()
  )
  .is_err());
}
