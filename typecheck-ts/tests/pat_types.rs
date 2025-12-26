use std::collections::HashMap;
use std::sync::Arc;

use hir_js::{lower_from_source, BodyKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::check::caches::CheckerCaches;
use typecheck_ts::check::hir_body::check_body;
use typecheck_ts::{BodyId, FileId};
use types_ts_interned::TypeStore;

#[test]
fn records_pattern_types_for_params_and_vars() {
  let source = "function add(a: number, b: number) { const c = a + b; return c; }";
  let lowered = lower_from_source(source).expect("lowering should succeed");
  let (body_id, body) = lowered
    .bodies
    .iter()
    .enumerate()
    .find(|(_, body)| matches!(body.kind, BodyKind::Function))
    .map(|(idx, b)| (BodyId(idx as u32), b.as_ref()))
    .expect("function body present");
  let names = Arc::clone(&lowered.names);
  let ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");

  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let bindings = HashMap::new();
  let mut next_symbol = 0;
  let (result, _) = check_body(
    body_id,
    body,
    &names,
    FileId(0),
    &ast,
    store.clone(),
    &caches,
    &bindings,
    &mut next_symbol,
    None,
    None,
    None,
  );
  let prim = store.primitive_ids();

  assert_eq!(result.pat_types().get(0), Some(&prim.number));
  assert_eq!(result.pat_types().get(1), Some(&prim.number));
  assert_eq!(result.pat_types().get(2), Some(&prim.number));
}
