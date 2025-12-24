use emit_js::{emit_interface_decl, emit_type_alias_decl};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{InterfaceDecl, TypeAliasDecl};

fn parse_type_alias(source: &str) -> Node<TypeAliasDecl> {
  let parsed = parse_js::parse(source).expect("parse failure");
  let TopLevel { body } = *parsed.stx;
  for stmt in body {
    if let Stmt::TypeAliasDecl(alias) = *stmt.stx {
      return alias;
    }
  }
  panic!("missing type alias");
}

fn parse_interface(source: &str) -> Node<InterfaceDecl> {
  let parsed = parse_js::parse(source).expect("parse failure");
  let TopLevel { body } = *parsed.stx;
  for stmt in body {
    if let Stmt::InterfaceDecl(decl) = *stmt.stx {
      return decl;
    }
  }
  panic!("missing interface");
}

fn emit_type_alias_to_string(decl: &Node<TypeAliasDecl>) -> String {
  let mut out = String::new();
  emit_type_alias_decl(&mut out, decl.stx.as_ref()).expect("emit failed");
  out
}

fn emit_interface_to_string(decl: &Node<InterfaceDecl>) -> String {
  let mut out = String::new();
  emit_interface_decl(&mut out, decl.stx.as_ref()).expect("emit failed");
  out
}

fn roundtrip_type_alias(source: &str, expected: &str) {
  let emitted = emit_type_alias_to_string(&parse_type_alias(source));
  assert_eq!(emitted, expected);

  let re_emitted = emit_type_alias_to_string(&parse_type_alias(&emitted));
  assert_eq!(re_emitted, expected);
}

fn roundtrip_interface(source: &str, expected: &str) {
  let emitted = emit_interface_to_string(&parse_interface(source));
  assert_eq!(emitted, expected);

  let re_emitted = emit_interface_to_string(&parse_interface(&emitted));
  assert_eq!(re_emitted, expected);
}

#[test]
fn emits_this_parameter_in_function_type() {
  roundtrip_type_alias(
    "type F=(this:Foo,x:number)=>void;",
    "type F = (this: Foo, x: number) => void;",
  );
}

#[test]
fn emits_this_parameter_in_call_signature() {
  roundtrip_interface(
    "interface I{(this:Foo,x:number):void}",
    "interface I {(this: Foo, x: number): void;}",
  );
}

#[test]
fn emits_typeof_queries_with_spacing() {
  roundtrip_type_alias("type T=typeof undefined;", "type T = typeof undefined;");
  roundtrip_type_alias("type T=typeof this;", "type T = typeof this;");
}
