use std::sync::Arc;

use diagnostics::FileId;
use hir_js::lower_from_source;
use typecheck_ts::check::hir_body::check_body;
use types_ts_interned::TypeStore;

#[test]
fn infers_basic_literals_and_identifiers() {
  let source = "function f(a) { return a; }";
  let lowered = lower_from_source(source).expect("lower");
  let body = lowered
    .bodies
    .iter()
    .find(|b| matches!(b.kind, hir_js::BodyKind::Function))
    .expect("function body");
  let store = TypeStore::new();
  let result = check_body(
    body,
    &lowered.names,
    FileId(0),
    source,
    Arc::clone(&store),
  );

  // parameter, const binding, return expression
  assert_eq!(result.expr_types.len(), body.exprs.len());
  assert_eq!(result.pat_types.len(), body.pats.len());
  assert!(
    !result.return_types.is_empty(),
    "return statement should be recorded"
  );
  assert!(result.diagnostics.is_empty());
}
