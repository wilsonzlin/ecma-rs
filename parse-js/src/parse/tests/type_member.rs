use crate::ast::stmt::Stmt;
use crate::ast::ts_stmt::InterfaceDecl;
use crate::ast::type_expr::{TypeMember, TypePropertyKey};
use crate::lex::Lexer;
use crate::parse::expr::pat::ParsePatternRules;
use crate::parse::{AsiContext, ParseCtx, Parser};
use crate::{Dialect, ParseOptions, SourceType};

fn parse_interface(input: &str) -> crate::ast::node::Node<InterfaceDecl> {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(input), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: false,
      yield_allowed: false,
      await_expr_allowed: true,
      yield_expr_allowed: false,
    },
    top_level: true,
    in_namespace: false,
    asi: AsiContext::Statements,
  };
  let stmt = parser.stmt(ctx).unwrap();
  match *stmt.stx {
    Stmt::InterfaceDecl(decl) => decl,
    other => panic!("expected interface declaration, got {:?}", other),
  }
}

#[test]
fn parses_interface_methods_named_get_and_set() {
  let decl = parse_interface(
    "interface Map<K, V> { get(key: K): V | undefined; set(key: K, value: V): this; }",
  );

  assert_eq!(decl.stx.members.len(), 2);

  let TypeMember::Method(get_method) = decl.stx.members[0].stx.as_ref() else {
    panic!("expected TypeMember::Method for Map.get");
  };
  assert!(matches!(
    &get_method.stx.key,
    TypePropertyKey::Identifier(name) if name == "get"
  ));

  let TypeMember::Method(set_method) = decl.stx.members[1].stx.as_ref() else {
    panic!("expected TypeMember::Method for Map.set");
  };
  assert!(matches!(
    &set_method.stx.key,
    TypePropertyKey::Identifier(name) if name == "set"
  ));
}

#[test]
fn parses_interface_generic_method_named_get() {
  let decl = parse_interface("interface Client { get<T>(path: string): Promise<T>; }");

  assert_eq!(decl.stx.members.len(), 1);
  let TypeMember::Method(method) = decl.stx.members[0].stx.as_ref() else {
    panic!("expected TypeMember::Method");
  };
  assert!(matches!(
    &method.stx.key,
    TypePropertyKey::Identifier(name) if name == "get"
  ));
  assert!(
    method.stx.type_parameters.is_some(),
    "expected `get<T>` to have type parameters"
  );
}

#[test]
fn parses_interface_get_accessor_signature() {
  let decl = parse_interface("interface X { get foo(): number; }");

  assert_eq!(decl.stx.members.len(), 1);
  let TypeMember::GetAccessor(accessor) = decl.stx.members[0].stx.as_ref() else {
    panic!("expected TypeMember::GetAccessor");
  };
  assert!(matches!(
    &accessor.stx.key,
    TypePropertyKey::Identifier(name) if name == "foo"
  ));
}
