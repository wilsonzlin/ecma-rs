use diagnostics::TextRange;
use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};
use std::sync::Arc;

#[test]
fn hir_file_emission_preserves_root_stmt_order_when_span_starts_tie() {
  let source = "a();b();c();";
  let mut lowered = lower_from_source_with_kind(FileKind::Js, source).expect("lower");

  let root_body_id = lowered.root_body();
  let root_body_idx = *lowered
    .body_index
    .get(&root_body_id)
    .expect("root body index");
  let body = Arc::make_mut(&mut lowered.bodies[root_body_idx]);

  assert!(
    body.root_stmts.len() >= 3,
    "expected at least 3 root statements"
  );

  // Force a tie on `span.start` so `emit_hir_file` must deterministically break
  // ties and preserve the original `root_stmts` ordering.
  for stmt_id in body.root_stmts.iter().take(3).copied() {
    let stmt = &mut body.stmts[stmt_id.0 as usize];
    stmt.span = TextRange::new(0, stmt.span.end);
  }

  let emitted = emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit");
  assert_eq!(emitted, source);
}
