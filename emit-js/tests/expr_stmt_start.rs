use emit_js::{emit_expr, emit_expr_stmt, emit_expr_stmt_with, expr_stmt_needs_parens, EmitResult};
use parse_js::ast::expr::{ClassExpr, Expr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{ExprStmt, Stmt};
use parse_js::ast::type_expr::TypeExpr;
use parse_js::parse;

fn with_expr_from_program(source: &str, f: impl FnOnce(&Node<Expr>)) {
  let program = parse(source).expect("source should parse");
  let first = program
    .stx
    .body
    .first()
    .expect("program should contain a statement");
  match first.stx.as_ref() {
    Stmt::Expr(expr_stmt) => f(&expr_stmt.stx.expr),
    other => panic!("expected expression statement, got {other:?}"),
  }
}

fn emit_expr_stmt_text(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr_stmt(&mut out, expr, &mut emit_type).expect("emit should succeed");
  assert_reparses_as_expr_stmt(&out);
  out
}

fn assert_reparses_as_expr_stmt(emitted: &str) {
  let reparsed = parse(&(emitted.to_string() + ";")).expect("emitted code should parse");
  let first = reparsed
    .stx
    .body
    .first()
    .expect("reparsed program should have a statement");
  assert!(
    matches!(first.stx.as_ref(), Stmt::Expr(_)),
    "expected expression statement after reparsing, got {first:?}"
  );
}

fn assert_needs_parens(source: &str) -> String {
  let mut emitted = String::new();
  with_expr_from_program(source, |expr| {
    assert!(
      expr_stmt_needs_parens(expr),
      "expected expression to require parentheses"
    );
    emitted = emit_expr_stmt_text(expr);
  });
  assert!(
    emitted.starts_with('('),
    "expected emitted expression to start with parentheses, got {emitted}"
  );
  emitted
}

#[test]
fn object_literal_statement_keeps_parens() {
  let emitted = assert_needs_parens("({a:1});");
  assert_eq!(emitted, "({a: 1})");
}

#[test]
fn function_expression_statement_is_parenthesized() {
  let emitted = assert_needs_parens("(function(){})");
  assert!(emitted.starts_with("(function"));
}

#[test]
fn class_expression_statement_is_parenthesized() {
  let emitted = assert_needs_parens("(class {})");
  assert!(emitted.starts_with("(class"));
}

#[test]
fn async_function_expression_statement_is_parenthesized() {
  let emitted = assert_needs_parens("(async function(){})");
  assert!(emitted.starts_with("(async function"));
}

#[test]
fn let_contextual_keyword_statement_is_disambiguated() {
  let emitted = assert_needs_parens("(let[x]=y)");
  assert!(emitted.starts_with("(let["));
}

#[test]
fn import_meta_statement_is_parenthesized() {
  let emitted = assert_needs_parens("(import.meta)");
  assert!(emitted.starts_with("(import.meta"));
}

#[test]
fn interface_and_type_identifiers_require_parens() {
  let interface_emitted = assert_needs_parens("((interface))");
  assert_eq!(interface_emitted, "(interface)");

  let type_emitted = assert_needs_parens("((type))");
  assert_eq!(type_emitted, "(type)");
}

#[test]
fn declare_tagged_template_does_not_need_parens() {
  with_expr_from_program("declare`tag`;", |expr| {
    assert!(
      !expr_stmt_needs_parens(expr),
      "declare tagged template should stay unparenthesized"
    );
  });
}

#[test]
fn declare_identifier_requires_parens() {
  let emitted = assert_needs_parens("((declare))");
  assert_eq!(emitted, "(declare)");
}

fn emit_class_expr(out: &mut String, class: &Node<ClassExpr>) -> EmitResult {
  for (idx, decorator) in class.stx.decorators.iter().enumerate() {
    if idx > 0 {
      out.push(' ');
    }
    out.push('@');
    let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
    emit_expr(out, &decorator.stx.expression, &mut emit_type)?;
    out.push(' ');
  }

  out.push_str("class");
  if let Some(name) = &class.stx.name {
    out.push(' ');
    out.push_str(&name.stx.name);
  }
  out.push_str(" {}");

  Ok(())
}

fn emit_expr_for_test(out: &mut String, expr: &Node<Expr>) -> EmitResult {
  match expr.stx.as_ref() {
    Expr::Class(class) => emit_class_expr(out, class),
    _ => {
      let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
      emit_expr(out, expr, &mut emit_type)
    }
  }
}

fn extract_expr_stmt(program: &Node<parse_js::ast::stx::TopLevel>) -> &Node<ExprStmt> {
  match program
    .stx
    .body
    .first()
    .expect("expected a statement")
    .stx
    .as_ref()
  {
    Stmt::Expr(stmt) => stmt,
    other => panic!("expected expression statement, found {:?}", other),
  }
}

#[test]
fn decorated_class_expr_stmt_roundtrips_with_parens() {
  let source = "(@dec class C {})";
  let parsed = parse_js::parse(source).expect("parse should succeed");
  let expr_stmt = extract_expr_stmt(&parsed);

  assert!(
    expr_stmt_needs_parens(&expr_stmt.stx.expr),
    "decorated class expressions should trigger parentheses"
  );

  let mut out = String::new();
  emit_expr_stmt_with(&mut out, &expr_stmt.stx.expr, emit_expr_for_test)
    .expect("emit should succeed");

  let reparsed = parse_js::parse(&out).expect("emitted code should parse");
  let original_json = serde_json::to_value(&parsed.stx).expect("serialize original");
  let reparsed_json = serde_json::to_value(&reparsed.stx).expect("serialize reparsed");
  assert_eq!(original_json, reparsed_json, "AST should roundtrip");
}
