use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ts_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

#[test]
fn async_arrow_with_type_parameters_is_parsed() {
  let ast = parse_with_options("async <T>(x: T) => x", ts_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let Stmt::Expr(stmt) = ast.stx.body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::ArrowFunc(arrow) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected arrow function expression");
  };

  assert!(arrow.stx.func.stx.async_);
  let type_parameters = arrow
    .stx
    .func
    .stx
    .type_parameters
    .as_ref()
    .expect("expected type parameters");
  assert_eq!(type_parameters.len(), 1);
  assert_eq!(type_parameters[0].stx.name, "T");
}
