use emit_js::{emit_stmt_top_level, Emitter};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;

fn assert_single_export_default_expr(top: &Node<TopLevel>) {
  let mut iter = top
    .stx
    .body
    .iter()
    .filter(|stmt| !matches!(stmt.stx.as_ref(), Stmt::Empty(_)));
  let first = iter.next().expect("expected at least one statement");
  assert!(
    iter.next().is_none(),
    "expected a single non-empty statement"
  );
  assert!(
    matches!(first.stx.as_ref(), Stmt::ExportDefaultExpr(_)),
    "expected export default expression, got {:?}",
    first.stx
  );
}

fn roundtrip(src: &str) {
  let parsed = parse_js::parse(src).expect("parse failed");
  assert_single_export_default_expr(&parsed);

  let mut emitter = Emitter::default();
  emit_stmt_top_level(&mut emitter, &parsed).expect("emit failed");
  let emitted = String::from_utf8(emitter.into_bytes()).expect("utf-8");

  let reparsed = parse_js::parse(&emitted).expect("reparse failed");
  assert_single_export_default_expr(&reparsed);
}

#[test]
fn export_default_function_expr_roundtrips() {
  roundtrip("export default (function() {})");
}

#[test]
fn export_default_class_expr_roundtrips() {
  roundtrip("export default (class {})");
}

#[test]
fn export_default_async_function_expr_roundtrips() {
  roundtrip("export default (async function() {})");
}
