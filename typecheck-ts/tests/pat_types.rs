use std::sync::Arc;

use hir_js::{lower_from_source, BodyKind};
use typecheck_ts::FileId;
use typecheck_ts::check::hir_body::check_body;
use types_ts_interned::TypeStore;

#[test]
fn records_pattern_types_for_params_and_vars() {
  let source = "function add(a: number, b: number) { const c = a + b; return c; }";
  let lowered = lower_from_source(source).expect("lowering should succeed");
  let body = lowered
    .bodies
    .iter()
    .find(|body| matches!(body.kind, BodyKind::Function))
    .map(|b| b.as_ref())
    .expect("function body present");
  let names = Arc::clone(&lowered.names);

  let store = TypeStore::new();
  let result = check_body(body, &names, FileId(0), source, store.clone());
  let prim = store.primitive_ids();

  assert_eq!(result.pat_types.get(0), Some(&prim.number));
  assert_eq!(result.pat_types.get(1), Some(&prim.number));
  assert_eq!(result.pat_types.get(2), Some(&prim.number));
}
