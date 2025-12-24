use emit_js::emit_type_alias_decl;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::TypeAliasDecl;

fn parse_type_alias(source: &str) -> Node<TypeAliasDecl> {
  let parsed = parse_js::parse(source).expect("parse failed");
  let TopLevel { body } = *parsed.stx;
  for stmt in body {
    if let Stmt::TypeAliasDecl(alias) = *stmt.stx {
      return alias;
    }
  }
  panic!("missing type alias");
}

fn emit_type_alias_to_string(decl: &Node<TypeAliasDecl>) -> String {
  let mut out = String::new();
  emit_type_alias_decl(&mut out, decl.stx.as_ref()).expect("emit type alias");
  out
}

fn roundtrip(src: &str, expected: &str) {
  let emitted = emit_type_alias_to_string(&parse_type_alias(src));
  assert_eq!(emitted, expected);

  let emitted_again = emit_type_alias_to_string(&parse_type_alias(&emitted));
  assert_eq!(emitted_again, expected);
}

#[test]
fn emits_nested_generic_type_arguments() {
  roundtrip("type T=Foo<Bar<Baz>>;", "type T = Foo<Bar<Baz>>;");
  roundtrip("type T=Foo<Bar<Baz<Qux>>>;", "type T = Foo<Bar<Baz<Qux>>>;");
  roundtrip("type T=A.B<C<D>>;", "type T = A.B<C<D>>;");
  roundtrip(
    "type T=import(\"m\").Foo<Bar<Baz>>;",
    "type T = import(\"m\").Foo<Bar<Baz>>;",
  );
}
