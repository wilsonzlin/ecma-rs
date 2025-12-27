mod util;

use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{Body, NameId, PatKind};
use typecheck_ts::check::flow_bindings::FlowBindings;
use typecheck_ts::check::hir_body::{base_body_result, refine_types_with_flow};
use typecheck_ts::codes;
use types_ts_interned::{RelateCtx, TypeId, TypeStore};

use crate::util::{body_of, parse_lower_with_locals};

const FILE_ID: FileId = FileId(0);

fn param_name(body: &Body, index: usize) -> NameId {
  let pat = body
    .function
    .as_ref()
    .expect("function body")
    .params
    .get(index)
    .expect("parameter exists");
  match &body.pats[pat.pat.0 as usize].kind {
    PatKind::Ident(name) => *name,
    other => panic!("expected ident param, got {other:?}"),
  }
}

fn run_flow(
  parsed: &util::Parsed,
  func: &str,
  store: &Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
) -> typecheck_ts::BodyCheckResult {
  let (body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, func);
  let relate = RelateCtx::new(Arc::clone(store), store.options());
  let flow_bindings = FlowBindings::new(body, &parsed.semantics);
  let prim = store.primitive_ids();
  let base = base_body_result(body_id, body, prim.unknown);
  refine_types_with_flow(
    body_id,
    body,
    &parsed.lowered.names,
    &flow_bindings,
    &parsed.semantics,
    FILE_ID,
    Arc::clone(store),
    &base,
    initial,
    relate,
    None,
  )
}

#[test]
fn assignment_on_all_paths() {
  let src =
    "function f(cond: boolean) { let x: number; if (cond) { x = 1; } else { x = 2; } return x; }";
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let (_body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, "f");
  initial.insert(param_name(body, 0), store.primitive_ids().boolean);
  let res = run_flow(&parsed, "f", &store, &initial);
  assert!(res.diagnostics().is_empty());
}

#[test]
fn missing_assignment_in_branch() {
  let src = "function f(cond: boolean) { let x: number; if (cond) { x = 1; } return x; }";
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let (_body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, "f");
  initial.insert(param_name(body, 0), store.primitive_ids().boolean);
  let res = run_flow(&parsed, "f", &store, &initial);
  assert_eq!(res.diagnostics().len(), 1);
  assert_eq!(
    res.diagnostics()[0].code.as_str(),
    codes::USE_BEFORE_ASSIGNMENT.as_str()
  );
}

#[test]
fn typeof_unassigned_allowed() {
  let src = "function f() { let x: number; return typeof x; }";
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let res = run_flow(&parsed, "f", &store, &HashMap::new());
  assert!(res.diagnostics().is_empty());
}

#[test]
fn shadowed_bindings_are_distinct() {
  let src =
    "function f(cond: boolean) { let x = 1; if (cond) { let x: number; x = 2; } return x; }";
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let (_body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, "f");
  initial.insert(param_name(body, 0), store.primitive_ids().boolean);
  let res = run_flow(&parsed, "f", &store, &initial);
  assert!(res.diagnostics().is_empty());
}

#[test]
fn loop_assignment_not_definite() {
  let src = "function f(cond: boolean) { let x: number; while (cond) { x = 1; } return x; }";
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let (_body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, "f");
  initial.insert(
    param_name(body, 0),
    store.primitive_ids().boolean,
  );
  let res = run_flow(&parsed, "f", &store, &initial);
  assert_eq!(res.diagnostics().len(), 1);
  assert_eq!(
    res.diagnostics()[0].code.as_str(),
    codes::USE_BEFORE_ASSIGNMENT.as_str()
  );
}
