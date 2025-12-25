use emit_js::{cooked_template_segment, emit_expr, EmitMode, EmitOptions, Emitter};
use parse_js::ast::expr::lit::LitTemplatePart;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;

#[derive(Debug, PartialEq, Eq)]
enum TemplatePartSignature {
  String(String),
  Substitution,
}

fn parse_expression(source: &str) -> Node<Expr> {
  let parsed = parse_js::parse(source).expect("parse failed");
  let TopLevel { mut body } = *parsed.stx;
  assert_eq!(body.len(), 1, "expected a single statement");
  let stmt = body.pop().expect("missing statement");
  match *stmt.stx {
    Stmt::Expr(expr_stmt) => expr_stmt.stx.expr,
    _ => panic!("expected expression statement"),
  }
}

fn template_parts(expr: &Expr) -> &[LitTemplatePart] {
  match expr {
    Expr::LitTemplate(template) => &template.stx.parts,
    Expr::TaggedTemplate(template) => &template.stx.parts,
    _ => panic!("expected template literal expression"),
  }
}

fn template_signature(expr: &Expr) -> Vec<TemplatePartSignature> {
  let parts = template_parts(expr);
  let len = parts.len();

  parts
    .iter()
    .enumerate()
    .map(|(idx, part)| match part {
      LitTemplatePart::String(value) => TemplatePartSignature::String(
        cooked_template_segment(value, idx == 0, idx + 1 == len).to_string(),
      ),
      LitTemplatePart::Substitution(_) => TemplatePartSignature::Substitution,
    })
    .collect()
}

fn emit_expr_in_mode(expr: &Node<Expr>, mode: EmitMode) -> String {
  let mut emitter = Emitter::new(EmitOptions { mode });
  emit_expr(&mut emitter, expr, |_, _| {
    unreachable!("no types in expression")
  })
  .expect("emit expression");
  String::from_utf8(emitter.into_bytes()).expect("emitted JS should be UTF-8")
}

fn assert_template_roundtrip(source: &str) {
  let expr = parse_expression(source);
  let expected = template_signature(expr.stx.as_ref());

  for mode in [EmitMode::Canonical, EmitMode::Minified] {
    let emitted = emit_expr_in_mode(&expr, mode);
    let reparsed = parse_expression(&format!("{emitted};"));
    let reparsed_signature = template_signature(reparsed.stx.as_ref());
    if reparsed_signature != expected {
      println!("emitted: {emitted}");
      println!("expected: {:?}", expected);
      println!("reparsed: {:?}", reparsed_signature);
    }
    assert_eq!(
      reparsed_signature, expected,
      "roundtrip mismatch for mode {:?}",
      mode
    );
  }
}

#[test]
fn emits_basic_template_literal() {
  assert_template_roundtrip("`a${b}c`;");
}

#[test]
fn emits_backticks_and_backslashes() {
  assert_template_roundtrip("`a\\`b\\\\${c}`;");
}

#[test]
fn preserves_literal_dollar_before_placeholder() {
  assert_template_roundtrip("`a$${b}`;");
}

#[test]
fn preserves_literal_placeholder_sequence() {
  assert_template_roundtrip("`keep\\${literal}`;");
}

#[test]
fn escapes_unicode_and_control_characters() {
  let source = "`line\\nwith\\rseparators\\u2028\\u2029\\u0001${value}`;";
  let expr = parse_expression(source);
  let emitted = emit_expr_in_mode(&expr, EmitMode::Canonical);
  assert!(
    emitted.contains("`line\\nwith\\rseparators\\u2028\\u2029\\x01${value}`"),
    "emitted string should escape line separators and control characters: {emitted}"
  );
  assert!(!emitted.contains('\n'));
  assert!(!emitted.contains('\r'));
  assert_template_roundtrip(source);
}

#[test]
fn emits_tagged_template_literal() {
  assert_template_roundtrip("tag`a\\`b${c}\\u2028`;");
}
