use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameInterner};
use typecheck_ts::check::hir_body::{check_body_with_env, FlowBindingId, FlowBindings};
use typecheck_ts::codes;
use types_ts_interned::{RelateCtx, TypeStore};

fn body_of<'a>(lowered: &'a LowerResult, names: &NameInterner, func: &str) -> (BodyId, &'a Body) {
  let def = lowered
    .defs
    .iter()
    .find(|d| names.resolve(d.name) == Some(func) && d.path.kind == DefKind::Function)
    .unwrap_or_else(|| panic!("missing function {func}"));
  let body_id = def.body.expect("function body");
  (body_id, lowered.body(body_id).unwrap())
}

fn run_flow(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  store: &Arc<TypeStore>,
  initial: &HashMap<FlowBindingId, types_ts_interned::TypeId>,
) -> typecheck_ts::BodyCheckResult {
  let relate = RelateCtx::new(Arc::clone(store), store.options());
  check_body_with_env(
    body_id,
    body,
    names,
    file,
    Arc::clone(store),
    None,
    initial,
    relate,
    None,
  )
}

#[test]
fn assignment_on_all_paths() {
  let src =
    "function f(cond: boolean) { let x: number; if (cond) { x = 1; } else { x = 2; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let bindings = FlowBindings::from_body(body);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let cond_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| bindings.binding_for_pat(p.pat))
    .expect("cond binding");
  initial.insert(cond_binding, store.primitive_ids().boolean);
  let res = run_flow(body_id, body, &lowered.names, FileId(0), &store, &initial);
  assert!(res.diagnostics().is_empty());
}

#[test]
fn missing_assignment_in_branch() {
  let src = "function f(cond: boolean) { let x: number; if (cond) { x = 1; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let bindings = FlowBindings::from_body(body);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let cond_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| bindings.binding_for_pat(p.pat))
    .expect("cond binding");
  initial.insert(cond_binding, store.primitive_ids().boolean);
  let res = run_flow(body_id, body, &lowered.names, FileId(0), &store, &initial);
  assert_eq!(res.diagnostics().len(), 1);
  assert_eq!(
    res.diagnostics()[0].code.as_str(),
    codes::USE_BEFORE_ASSIGNMENT.as_str()
  );
}

#[test]
fn typeof_unassigned_allowed() {
  let src = "function f() { let x: number; return typeof x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let res = run_flow(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    &store,
    &HashMap::new(),
  );
  assert!(res.diagnostics().is_empty());
}

#[test]
fn shadowed_bindings_are_distinct() {
  let src =
    "function f(cond: boolean) { let x = 1; if (cond) { let x: number; x = 2; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let bindings = FlowBindings::from_body(body);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let cond_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| bindings.binding_for_pat(p.pat))
    .expect("cond binding");
  initial.insert(cond_binding, store.primitive_ids().boolean);
  let res = run_flow(body_id, body, &lowered.names, FileId(0), &store, &initial);
  assert!(res.diagnostics().is_empty());
}

#[test]
fn loop_assignment_not_definite() {
  let src = "function f(cond: boolean) { let x: number; while (cond) { x = 1; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let bindings = FlowBindings::from_body(body);
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let cond_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| bindings.binding_for_pat(p.pat))
    .expect("cond binding");
  initial.insert(cond_binding, store.primitive_ids().boolean);
  let res = run_flow(body_id, body, &lowered.names, FileId(0), &store, &initial);
  assert_eq!(res.diagnostics().len(), 1);
  assert_eq!(
    res.diagnostics()[0].code.as_str(),
    codes::USE_BEFORE_ASSIGNMENT.as_str()
  );
}
