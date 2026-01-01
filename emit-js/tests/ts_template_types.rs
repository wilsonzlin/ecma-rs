use emit_js::{emit_template_literal_segment, ts_type_to_string, EmitMode};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::{TypeEntityName, TypeExpr, TypeReference, TypeTemplateLiteral};

fn emit_type_expr_to_string(expr: &Node<TypeExpr>) -> String {
  ts_type_to_string(expr, EmitMode::Canonical)
}

fn parse_template_type_expr(source: &str) -> Node<TypeExpr> {
  let parsed = parse_js::parse(source).expect("parse failed");
  let TopLevel { body } = *parsed.stx;

  for stmt in body {
    if let Stmt::TypeAliasDecl(alias) = *stmt.stx {
      return alias.stx.type_expr;
    }
  }

  panic!("missing type alias");
}

fn extract_template_literal(expr: &TypeExpr) -> &Node<TypeTemplateLiteral> {
  match expr {
    TypeExpr::TemplateLiteralType(template) => template,
    _ => panic!("expected template literal type"),
  }
}

fn type_expr_to_string(expr: &TypeExpr) -> String {
  match expr {
    TypeExpr::TypeReference(reference) => type_reference_to_string(reference),
    _ => panic!("unexpected type expression in template span"),
  }
}

fn type_reference_to_string(reference: &Node<TypeReference>) -> String {
  let mut out = String::new();
  push_entity_name(&mut out, &reference.stx.name);

  if let Some(args) = &reference.stx.type_arguments {
    out.push('<');
    for (i, arg) in args.iter().enumerate() {
      if i > 0 {
        out.push_str(", ");
      }
      out.push_str(&type_expr_to_string(&arg.stx));
    }
    out.push('>');
  }

  out
}

fn push_entity_name(out: &mut String, name: &TypeEntityName) {
  match name {
    TypeEntityName::Identifier(id) => out.push_str(id),
    TypeEntityName::Qualified(qualified) => {
      push_entity_name(out, &qualified.left);
      out.push('.');
      out.push_str(&qualified.right);
    }
    TypeEntityName::Import(_) => panic!("unsupported import entity"),
  }
}

fn expected_output(template: &TypeTemplateLiteral) -> String {
  let mut out = Vec::new();
  out.push(b'`');

  emit_template_literal_segment(&mut out, &template.head);
  for span in &template.spans {
    out.extend_from_slice(b"${");
    out.extend_from_slice(type_expr_to_string(&span.stx.type_expr.stx).as_bytes());
    out.push(b'}');
    emit_template_literal_segment(&mut out, &span.stx.literal);
  }

  out.push(b'`');
  String::from_utf8(out).expect("expected output is UTF-8")
}

fn assert_roundtrip(source: &str) {
  let type_expr = parse_template_type_expr(source);
  let template = extract_template_literal(type_expr.stx.as_ref());

  let expected = expected_output(template.stx.as_ref());
  let emitted = emit_type_expr_to_string(&type_expr);
  assert_eq!(
    emitted, expected,
    "emitted template literal did not match expectation"
  );

  let reparsed = parse_template_type_expr(&format!("type T = {emitted};"));
  let reparsed_template = extract_template_literal(reparsed.stx.as_ref());
  assert_eq!(reparsed_template.stx.spans.len(), template.stx.spans.len());

  let re_emitted = emit_type_expr_to_string(&reparsed);
  assert_eq!(re_emitted, emitted, "emission should be idempotent");
}

#[test]
fn template_literal_type_basic() {
  assert_roundtrip("type T = `foo${T}bar`");
}

#[test]
fn template_literal_type_with_dollar_literal() {
  assert_roundtrip("type T = `a${T}$b`");
}

#[test]
fn template_literal_type_with_backslashes_and_backticks() {
  assert_roundtrip(r"type T = `\\\`${T}\\`");
}
