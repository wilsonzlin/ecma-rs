use emit_js::emit_type_alias_decl;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::TypeAliasDecl;

fn parse_type_alias(src: &str) -> Node<TypeAliasDecl> {
  let top = parse_js::parse(src).expect("parse failed");
  let TopLevel { mut body } = *top.stx;
  let stmt = body.pop().expect("expected a statement");
  match *stmt.stx {
    Stmt::TypeAliasDecl(type_alias) => type_alias,
    other => panic!("unexpected statement: {:?}", other),
  }
}

fn emit_type_alias_to_string(decl: &Node<TypeAliasDecl>) -> String {
  let mut out = String::new();
  emit_type_alias_decl(&mut out, decl.stx.as_ref()).expect("emit should succeed");
  out
}

#[test]
fn type_alias_roundtrip() {
  let alias = parse_type_alias("type Foo<T extends U = V> = T | U;");
  let emitted = emit_type_alias_to_string(&alias);
  assert_eq!(emitted, "type Foo<T extends U = V> = T | U;");

  let reparsed = parse_type_alias(&emitted);
  assert_eq!(alias.stx.name, reparsed.stx.name);
  assert_eq!(alias.stx.export, reparsed.stx.export);
  assert_eq!(alias.stx.declare, reparsed.stx.declare);
  let re_emitted = emit_type_alias_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}
