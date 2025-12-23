use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::type_expr::{
  TypeEntityName, TypeExpr, TypeMember, TypePredicate, TypeReference,
};
use parse_js::parse;

fn parse_predicate_from_interface(src: &str) -> TypePredicate {
  let top_level = parse(src).expect("failed to parse interface");

  let Node { stx: top_stx, .. } = top_level;
  let mut body_iter = top_stx.body.into_iter();
  let stmt = body_iter
    .next()
    .expect("expected interface statement");

  let interface = match *stmt.stx {
    Stmt::InterfaceDecl(interface) => interface,
    other => panic!("expected interface declaration, got {:?}", other),
  };

  let mut members = interface.stx.members.into_iter();
  let member = members
    .next()
    .expect("expected interface to have a member");

  let method = match *member.stx {
    TypeMember::Method(method) => method,
    other => panic!("expected method signature, got {:?}", other),
  };

  let return_type = method
    .stx
    .return_type
    .expect("expected method to have return type");

  match *return_type.stx {
    TypeExpr::TypePredicate(predicate) => *predicate.stx,
    other => panic!("expected type predicate return type, got {:?}", other),
  }
}

fn emit_type_expr(expr: &TypeExpr) -> String {
  match expr {
    TypeExpr::TypeReference(reference) => emit_type_reference(reference.stx.as_ref()),
    TypeExpr::TypePredicate(predicate) => emit_type_predicate(predicate.stx.as_ref()),
    other => panic!("unsupported type expression in test emitter: {:?}", other),
  }
}

fn emit_type_reference(reference: &TypeReference) -> String {
  match &reference.name {
    TypeEntityName::Identifier(name) => name.clone(),
    other => panic!("unsupported type reference in test emitter: {:?}", other),
  }
}

fn emit_type_predicate(predicate: &TypePredicate) -> String {
  let mut out = String::new();
  if predicate.asserts {
    out.push_str("asserts ");
  }
  out.push_str(&predicate.parameter_name);
  if let Some(annotation) = predicate.type_annotation.as_ref() {
    out.push_str(" is ");
    out.push_str(&emit_type_expr(annotation.stx.as_ref()));
  }
  out
}

#[test]
fn parses_this_type_predicate_return_type() {
  let predicate = parse_predicate_from_interface("interface I{isFoo():this is Foo}");

  assert!(!predicate.asserts);
  assert_eq!(predicate.parameter_name, "this");

  let type_annotation = predicate
    .type_annotation
    .as_ref()
    .expect("expected type annotation for predicate");
  match type_annotation.stx.as_ref() {
    TypeExpr::TypeReference(reference) => match &reference.stx.name {
      TypeEntityName::Identifier(name) => assert_eq!(name, "Foo"),
      other => panic!("unexpected type reference name: {:?}", other),
    },
    other => panic!("unexpected type annotation: {:?}", other),
  }

  assert_eq!(emit_type_predicate(&predicate), "this is Foo");
}

#[test]
fn parses_asserts_identifier_predicate_without_type() {
  let predicate = parse_predicate_from_interface("interface I{assertFoo(x:any):asserts x}");

  assert!(predicate.asserts);
  assert_eq!(predicate.parameter_name, "x");
  assert!(predicate.type_annotation.is_none());

  assert_eq!(emit_type_predicate(&predicate), "asserts x");
}

#[test]
fn parses_asserts_this_predicate() {
  let predicate = parse_predicate_from_interface("interface I{assertThis():asserts this is Foo}");

  assert!(predicate.asserts);
  assert_eq!(predicate.parameter_name, "this");

  let type_annotation = predicate
    .type_annotation
    .as_ref()
    .expect("expected type annotation for predicate");
  match type_annotation.stx.as_ref() {
    TypeExpr::TypeReference(reference) => match &reference.stx.name {
      TypeEntityName::Identifier(name) => assert_eq!(name, "Foo"),
      other => panic!("unexpected type reference name: {:?}", other),
    },
    other => panic!("unexpected type annotation: {:?}", other),
  }

  assert_eq!(emit_type_predicate(&predicate), "asserts this is Foo");
}
