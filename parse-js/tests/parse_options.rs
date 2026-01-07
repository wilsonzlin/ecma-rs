use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn opts(dialect: Dialect, source_type: SourceType) -> ParseOptions {
  ParseOptions {
    dialect,
    source_type,
  }
}

#[test]
fn js_dialect_treats_ts_keywords_as_identifiers() {
  let js_opts = opts(Dialect::Js, SourceType::Script);
  let js_ast = parse_with_options("type Foo = number;", js_opts).expect("js parse should succeed");
  match js_ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(_) => {}
    other => panic!("expected expression statement in JS mode, got {other:?}"),
  }

  let ecma_opts = opts(Dialect::Ecma, SourceType::Script);
  assert!(parse_with_options("type Foo = number;", ecma_opts).is_err());

  let ts_opts = opts(Dialect::Ts, SourceType::Script);
  let ts_ast =
    parse_with_options("type Foo = number;", ts_opts).expect("ts type alias should parse");
  match ts_ast.stx.body[0].stx.as_ref() {
    Stmt::TypeAliasDecl(_) => {}
    other => panic!("expected type alias in TS mode, got {other:?}"),
  }
}

#[test]
fn tsx_disallows_angle_bracket_type_assertions() {
  let ts_opts = opts(Dialect::Ts, SourceType::Module);
  assert!(parse_with_options("<Foo>bar;", ts_opts).is_ok());

  let tsx_opts = opts(Dialect::Tsx, SourceType::Module);
  assert!(parse_with_options("<Foo>bar;", tsx_opts).is_err());
}

#[test]
fn script_source_type_rejects_module_syntax() {
  let script_opts = opts(Dialect::Js, SourceType::Script);
  assert!(parse_with_options("import x from 'y';", script_opts).is_err());
  assert!(parse_with_options("export const x = 1;", script_opts).is_err());
}
