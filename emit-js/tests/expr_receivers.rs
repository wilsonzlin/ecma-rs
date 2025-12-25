use emit_js::{emit_expr, emit_type_expr};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{ExprStmt, Stmt};
use parse_js::ast::stx::TopLevel;

fn parse_expression(source: &str) -> Node<Expr> {
  let program = parse_js::parse(&format!("{};", source)).expect("parse failure");
  let TopLevel { mut body } = *program.stx;
  assert_eq!(body.len(), 1, "expected a single statement");
  match *body.pop().unwrap().stx {
    Stmt::Expr(expr_stmt) => {
      let ExprStmt { expr } = *expr_stmt.stx;
      expr
    }
    other => panic!("unexpected statement: {:?}", other),
  }
}

fn emit_expression(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  emit_expr(&mut out, expr, emit_type_expr).expect("emit failed");
  out
}

fn assert_roundtrip(source: &str, expected_emitted: &str) {
  let parsed = parse_expression(source);
  let emitted = emit_expression(&parsed);
  assert_eq!(emitted, expected_emitted);

  let reparsed = parse_expression(&emitted);

  let original_json = serde_json::to_value(&parsed).expect("serialize parsed");
  let reparsed_json = serde_json::to_value(&reparsed).expect("serialize reparsed");
  assert_eq!(
    original_json, reparsed_json,
    "roundtrip mismatch for `{}`",
    source
  );
}

#[test]
fn type_assertion_member_receiver_is_parenthesized() {
  assert_roundtrip("(x as any).y", "(x as any).y");
}

#[test]
fn satisfies_member_receiver_is_parenthesized() {
  assert_roundtrip("(x satisfies T).y", "(x satisfies T).y");
}

#[test]
fn type_assertion_call_receiver_is_parenthesized() {
  assert_roundtrip("(x as any)()", "(x as any)()");
}

#[test]
fn satisfies_call_receiver_is_parenthesized() {
  assert_roundtrip("(x satisfies T)()", "(x satisfies T)()");
}

#[test]
fn satisfies_optional_member_receiver_is_parenthesized() {
  assert_roundtrip("(x satisfies T)?.y", "(x satisfies T)?.y");
}

#[test]
fn satisfies_optional_call_receiver_is_parenthesized() {
  assert_roundtrip("(x satisfies T)?.()", "(x satisfies T)?.()");
}

#[test]
fn type_assertion_computed_member_receiver_is_parenthesized() {
  assert_roundtrip("(x as any)[y]", "(x as any)[y]");
}

#[test]
fn type_assertion_optional_member_receiver_is_parenthesized() {
  assert_roundtrip("(x as any)?.y", "(x as any)?.y");
}

#[test]
fn type_assertion_optional_call_receiver_is_parenthesized() {
  assert_roundtrip("(x as any)?.()", "(x as any)?.()");
}

#[test]
fn type_assertion_optional_computed_member_receiver_is_parenthesized() {
  assert_roundtrip("(x as any)?.[y]", "(x as any)?.[y]");
}
