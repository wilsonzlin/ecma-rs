use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::type_expr::{
  TypeEntityName, TypeExpr, TypeFunctionParameter, TypeMember, TypePredicate, TypePropertyKey,
  TypeReference,
};
use parse_js::parse;

fn parse_interface(src: &str) -> InterfaceDecl {
  let Node { stx: top_stx, .. } = parse(src).expect("failed to parse interface");
  let mut body_iter = top_stx.body.into_iter();
  let stmt = body_iter.next().expect("expected interface statement");

  match *stmt.stx {
    Stmt::InterfaceDecl(interface) => *interface.stx,
    other => panic!("expected interface declaration, got {:?}", other),
  }
}

fn parse_predicate_from_interface(src: &str) -> TypePredicate {
  let interface = parse_interface(src);

  let mut members = interface.members.into_iter();
  let member = members.next().expect("expected interface to have a member");

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
    TypeExpr::Any(_) => "any".to_string(),
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

fn emit_function_parameter(param: &TypeFunctionParameter) -> String {
  let mut out = String::new();
  if param.rest {
    out.push_str("...");
  }
  if let Some(name) = param.name.as_ref() {
    out.push_str(name);
    if param.optional {
      out.push('?');
    }
  }
  out.push(':');
  out.push_str(&emit_type_expr(param.type_expr.stx.as_ref()));
  out
}

fn emit_type_member(member: &TypeMember) -> String {
  match member {
    TypeMember::Method(method) => {
      let mut out = String::new();
      match &method.stx.key {
        TypePropertyKey::Identifier(name) => out.push_str(name),
        other => panic!("unsupported method key in test emitter: {:?}", other),
      }
      if method.stx.optional {
        out.push('?');
      }
      out.push('(');
      let mut params = method.stx.parameters.iter();
      if let Some(first) = params.next() {
        out.push_str(&emit_function_parameter(first.stx.as_ref()));
        for param in params {
          out.push(',');
          out.push_str(&emit_function_parameter(param.stx.as_ref()));
        }
      }
      out.push(')');
      if let Some(return_type) = method.stx.return_type.as_ref() {
        out.push(':');
        out.push_str(&emit_type_expr(return_type.stx.as_ref()));
      }
      out
    }
    other => panic!("unsupported type member in test emitter: {:?}", other),
  }
}

fn emit_interface(interface: &InterfaceDecl) -> String {
  let mut out = String::new();
  out.push_str("interface ");
  out.push_str(&interface.name);
  out.push('{');
  for member in &interface.members {
    out.push_str(&emit_type_member(member.stx.as_ref()));
  }
  out.push('}');
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
fn roundtrips_this_type_predicate_method_signature() {
  let src = "interface I{isFoo():this is Foo}";
  let interface = parse_interface(src);
  assert_eq!(emit_interface(&interface), src);
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
fn roundtrips_asserts_identifier_predicate_method_signature() {
  let src = "interface I{assertFoo(x:any):asserts x}";
  let interface = parse_interface(src);
  assert_eq!(emit_interface(&interface), src);
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

#[test]
fn roundtrips_asserts_this_predicate_method_signature() {
  let src = "interface I{assertThis():asserts this is Foo}";
  let interface = parse_interface(src);
  assert_eq!(emit_interface(&interface), src);
}
