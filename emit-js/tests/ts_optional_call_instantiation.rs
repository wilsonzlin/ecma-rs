use diagnostics::FileId;
use emit_js::{
  emit_expr, emit_js_top_level, emit_top_level_diagnostic, emit_type_expr, EmitOptions, Emitter,
};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::TypeExpr;

fn first_expr(top: &Node<TopLevel>) -> &Node<Expr> {
  let stmt = top
    .stx
    .body
    .first()
    .expect("expected at least one statement");
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
    other => panic!("expected expression statement, got {other:?}"),
  }
}

#[test]
fn emits_optional_chaining_call_type_args_after_chain_token_emitter() {
  let source = "fn?.<string>(x);";
  let parsed = parse_js::parse(source).expect("parse TS");

  let emitted =
    emit_top_level_diagnostic(FileId(0), &parsed, EmitOptions::canonical()).expect("emit TS");

  assert!(
    emitted.contains("?.<string>"),
    "expected `?.<string>` in output, got `{emitted}`"
  );
  assert!(
    !emitted.contains("<string>?."),
    "type arguments must appear after `?.`, got `{emitted}`"
  );

  let reparsed = parse_js::parse(&emitted).expect("reparse emitted TS");
  let left = serde_json::to_value(&parsed).expect("serialize original AST");
  let right = serde_json::to_value(&reparsed).expect("serialize reparsed AST");
  assert_eq!(left, right, "token emitter should roundtrip");
}

#[test]
fn emits_optional_chaining_call_type_args_after_chain_fmt_emitter() {
  let source = "fn?.<string>(x);";
  let parsed = parse_js::parse(source).expect("parse TS");
  let expr = first_expr(&parsed);

  let mut emitted = String::new();
  let mut emit_type = |out: &mut String, ty: &Node<TypeExpr>| emit_type_expr(out, ty);
  emit_expr(&mut emitted, expr, &mut emit_type).expect("emit expression");

  assert!(
    emitted.contains("?.<string>"),
    "expected `?.<string>` in output, got `{emitted}`"
  );
  assert!(
    !emitted.contains("<string>?."),
    "type arguments must appear after `?.`, got `{emitted}`"
  );

  let reparsed = parse_js::parse(&format!("{emitted};")).expect("reparse emitted TS expression");
  let reparsed_expr = first_expr(&reparsed);
  let left = serde_json::to_value(expr).expect("serialize original expr AST");
  let right = serde_json::to_value(reparsed_expr).expect("serialize reparsed expr AST");
  assert_eq!(left, right, "fmt emitter should roundtrip");
}

#[test]
fn js_emitter_erases_type_arguments_from_optional_chaining_call() {
  let source = "fn?.<string>(x);";
  let parsed = parse_js::parse(source).expect("parse TS");

  let mut emitter = Emitter::new(EmitOptions::minified());
  emit_js_top_level(&mut emitter, parsed.stx.as_ref()).expect("emit JS");
  let out = String::from_utf8(emitter.into_bytes()).expect("JS output is UTF-8");

  assert!(
    out.contains("fn?.(x)"),
    "expected JS emitter to erase type args, got `{out}`"
  );
  assert!(
    !out.contains('<'),
    "JS output must not contain `<`: `{out}`"
  );
  assert!(
    !out.contains('>'),
    "JS output must not contain `>`: `{out}`"
  );
}
