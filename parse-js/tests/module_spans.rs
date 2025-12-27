use parse_js::ast::stmt::Stmt;
use parse_js::loc::Loc;
use parse_js::parse;

#[test]
fn module_decl_records_name_span() {
  let src = r#"declare module "ambient" {}"#;
  let ast = parse(src).expect("parse ambient module");
  let stmt = ast.stx.body.first().expect("statement present");
  let module = match stmt.stx.as_ref() {
    Stmt::ModuleDecl(module) => module,
    other => panic!("expected module decl, got {other:?}"),
  };

  let string = "\"ambient\"";
  let start = src.find(string).expect("string literal present");
  let expected = Loc(start, start + string.len());
  assert_eq!(module.stx.name_loc, expected);
}
