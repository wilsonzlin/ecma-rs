//! Incremental behavior of the salsa-tracked body-check query.
//!
//! `Program::body_check_count()` counts actual executions of the tracked
//! `check_body` query (memo hits do not increment it), so deltas across edits
//! show exactly which bodies were re-checked.

use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

fn program_with_two_files() -> (Program, FileKey, FileKey) {
  let mut host = MemoryHost::new();
  let a = FileKey::new("a.ts");
  let b = FileKey::new("b.ts");
  host.insert(a.clone(), "export function fa(): number { return 1; }\n");
  host.insert(
    b.clone(),
    "import { fa } from \"./a\";\nexport function fb(): number { return fa() + 1; }\n",
  );
  let program = Program::new(host, vec![a.clone(), b.clone()]);
  (program, a, b)
}

#[test]
fn repeated_check_reuses_all_body_results() {
  let (program, _a, _b) = program_with_two_files();
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean program, got {diagnostics:?}"
  );
  let after_first = program.body_check_count();
  assert!(after_first > 0, "first check must execute body checks");

  let _ = program.check();
  assert_eq!(
    program.body_check_count(),
    after_first,
    "re-checking without edits must not re-run any body checks"
  );
}

#[test]
fn body_edit_rechecks_only_the_edited_files_bodies() {
  let (mut program, a, _b) = program_with_two_files();
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean program, got {diagnostics:?}"
  );
  let file_a = program.file_id(&a).expect("file id for a.ts");
  let a_bodies = program.bodies_in_file(file_a).len();
  assert!(a_bodies > 0, "a.ts must have bodies");
  let before_edit = program.body_check_count();

  // Body-only edit in a.ts: declaration types, spans, and exports all stay
  // identical, so the published body-check context backdates and only bodies
  // whose file actually changed (a.ts) are re-checked. In particular b.ts,
  // which *imports* from a.ts, is untouched.
  program.set_file_text(
    file_a,
    Arc::from("export function fa(): number { return 2; }\n"),
  );
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean program after edit, got {diagnostics:?}"
  );

  let delta = program.body_check_count() - before_edit;
  assert_eq!(
    delta, a_bodies,
    "a body edit must re-check exactly the edited file's bodies"
  );
}

#[test]
fn decl_type_edit_rechecks_dependent_bodies() {
  let (mut program, a, b) = program_with_two_files();
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean program, got {diagnostics:?}"
  );
  let file_a = program.file_id(&a).expect("file id for a.ts");
  let file_b = program.file_id(&b).expect("file id for b.ts");

  // Changing fa's declared return type must invalidate the body-check context
  // (interned declaration types differ), so b.ts — whose body calls fa() — is
  // re-checked and reports the new arithmetic error. This is the stale-result
  // guard for context backdating: over-eager equality here would keep b's old
  // clean result alive.
  program.set_file_text(
    file_a,
    Arc::from("export function fa(): string { return \"1\"; }\n"),
  );
  let diagnostics = program.check();
  assert!(
    diagnostics.iter().any(|diag| diag.primary.file == file_b),
    "expected a diagnostic in b.ts after fa's return type changed, got {diagnostics:?}"
  );
}
