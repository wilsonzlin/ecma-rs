use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn const_typeof_annotation_does_not_overflow_stack() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("entry.ts");
  host.insert(
    file.clone(),
    Arc::<str>::from(
      r#"
export const inferred = { a: 1, b: "ok" };
export const ok: typeof inferred = { a: 1, b: "ok" };
"#
      .to_string(),
    ),
  );

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
}
