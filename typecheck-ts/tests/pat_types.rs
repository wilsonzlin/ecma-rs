use std::collections::HashMap;
use std::sync::Arc;

use hir_js::{lower_from_source, BodyKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::check::caches::CheckerCaches;
use typecheck_ts::check::hir_body::check_body;
use typecheck_ts::check::hir_body::AstIndex;
use typecheck_ts::{FileId, PatId};
use types_ts_interned::TypeStore;

#[test]
fn records_pattern_types_for_params_and_vars() {
  let source = "function add(a: number, b: number) { const c = a + b; return c; }";
  let lowered = lower_from_source(source).expect("lowering should succeed");
  let (body_id, body) = lowered
    .hir
    .bodies
    .iter()
    .copied()
    .filter_map(|id| lowered.body(id).map(|b| (id, b)))
    .find(|(_, body)| matches!(body.kind, BodyKind::Function))
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
  let ast = Arc::new(ast);
  let ast_index = AstIndex::new(Arc::clone(&ast), FileId(0), None);

  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let bindings = HashMap::new();
  let result = check_body(
    body_id,
    body,
    &names,
    FileId(0),
    &ast_index,
    store.clone(),
    &caches,
    &bindings,
    None,
  );
  let prim = store.primitive_ids();

  assert_eq!(result.pat_type(PatId(0)), Some(prim.number));
  assert_eq!(result.pat_type(PatId(1)), Some(prim.number));
  assert_eq!(result.pat_type(PatId(2)), Some(prim.number));
}
