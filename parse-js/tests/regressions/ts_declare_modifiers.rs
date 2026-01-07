use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ts_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

fn ts_module_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  }
}

#[test]
fn declare_async_function_is_async() {
  let ast = parse_with_options("declare async function f();", ts_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let Stmt::FunctionDecl(decl) = ast.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  assert!(decl.stx.function.stx.async_);
}

#[test]
fn declare_abstract_class_is_abstract() {
  let ast = parse_with_options("declare abstract class C {}", ts_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let Stmt::ClassDecl(decl) = ast.stx.body[0].stx.as_ref() else {
    panic!("expected class declaration");
  };
  assert!(decl.stx.declare);
  assert!(decl.stx.abstract_);
}

#[test]
fn export_declare_propagates_export_flag() {
  let ast = parse_with_options(
    "export declare async function f();\nexport declare class C {}\nexport declare const x: number;",
    ts_module_opts(),
  )
  .unwrap();
  assert_eq!(ast.stx.body.len(), 3);

  let Stmt::FunctionDecl(decl) = ast.stx.body[0].stx.as_ref() else {
    panic!("expected function declaration");
  };
  assert!(decl.stx.export);
  assert!(decl.stx.function.stx.async_);

  let Stmt::ClassDecl(decl) = ast.stx.body[1].stx.as_ref() else {
    panic!("expected class declaration");
  };
  assert!(decl.stx.export);
  assert!(decl.stx.declare);

  let Stmt::VarDecl(decl) = ast.stx.body[2].stx.as_ref() else {
    panic!("expected variable declaration");
  };
  assert!(decl.stx.export);
  assert_eq!(decl.stx.mode, VarDeclMode::Const);
}
