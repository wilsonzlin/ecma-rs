use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::ast::type_expr::{TypeExpr, TypeFunction};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ts_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

#[test]
fn bare_function_type_param_is_named_with_any() {
  let ast = parse_with_options("type F = (x) => number;", ts_script_opts()).expect("parse");
  let Stmt::TypeAliasDecl(alias) = ast.stx.body[0].stx.as_ref() else {
    panic!("expected type alias, got {:?}", ast.stx.body[0].stx);
  };
  let TypeAliasDecl { type_expr: ty, .. } = alias.stx.as_ref();
  let TypeExpr::FunctionType(func) = ty.stx.as_ref() else {
    panic!("expected function type, got {:?}", ty.stx);
  };
  let TypeFunction { parameters, .. } = func.stx.as_ref();
  assert_eq!(parameters.len(), 1);
  assert_eq!(parameters[0].stx.name.as_deref(), Some("x"));
  assert!(
    matches!(parameters[0].stx.type_expr.stx.as_ref(), TypeExpr::Any(_)),
    "expected synthetic any, got {:?}",
    parameters[0].stx.type_expr.stx
  );
}
