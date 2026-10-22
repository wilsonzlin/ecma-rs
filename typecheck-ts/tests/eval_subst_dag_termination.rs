//! Termination guard: `substitute_only` in the type evaluator memoizes shared
//! substructure per `evaluate_ref` invocation. Interned types are DAGs, and
//! self-similar intersection/mapped types (`OldDiff<keyof this, keyof A>` in
//! `conditionalTypes1.ts`) otherwise made the structural substitution walk
//! explode exponentially — the checker never finished the file (observed:
//! >58 minutes of CPU before the fix; ~20s after, debug build).

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn conditional_types1_terminates() {
  let src = include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/types/conditional/conditionalTypes1.ts"
  );
  let mut host = MemoryHost::default();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  // Completion is the assertion: before the DAG-sharing memo this did not
  // finish. No ICE diagnostics are allowed either way.
  let diags = program.check();
  assert!(
    diags.iter().all(|d| !d.code.as_str().starts_with("ICE")),
    "unexpected ICE diagnostics: {:?}",
    diags
      .iter()
      .filter(|d| d.code.as_str().starts_with("ICE"))
      .collect::<Vec<_>>()
  );
}
