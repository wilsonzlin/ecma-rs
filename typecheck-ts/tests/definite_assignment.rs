use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameId, NameInterner};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::check::caches::CheckerCaches;
use typecheck_ts::check::flow_bindings::FlowBindings;
use typecheck_ts::check::hir_body::{check_body_with_expander, refine_types_with_flow};
use typecheck_ts::codes;
use typecheck_ts::lib_support::CacheOptions;
use types_ts_interned::{RelateCtx, RelateHooks, TypeStore};

fn name_id(names: &NameInterner, target: &str) -> NameId {
  let mut clone = names.clone();
  clone.intern(target)
}

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
  src: &str,
  store: &Arc<TypeStore>,
  initial: &HashMap<NameId, types_ts_interned::TypeId>,
) -> typecheck_ts::BodyCheckResult {
  let parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let caches = CheckerCaches::new(CacheOptions::default()).for_body();
  let flow_bindings = FlowBindings::from_body(body);
  let hooks = RelateHooks::default();
  let relate = RelateCtx::with_hooks_and_cache(
    Arc::clone(store),
    store.options(),
    hooks,
    caches.relation.clone(),
  );
  let base_bindings: HashMap<String, types_ts_interned::TypeId> = initial
    .iter()
    .filter_map(|(name, ty)| names.resolve(*name).map(|name| (name.to_string(), *ty)))
    .collect();
  let base = check_body_with_expander(
    body_id,
    body,
    names,
    file,
    &parsed,
    Arc::clone(store),
    &caches,
    &base_bindings,
    None,
    None,
    None,
  );
  refine_types_with_flow(
    body_id,
    body,
    names,
    &flow_bindings,
    file,
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
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "cond"),
    store.primitive_ids().boolean,
  );
  let res = run_flow(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    &store,
    &initial,
  );
  assert!(res.diagnostics().is_empty());
}

#[test]
fn missing_assignment_in_branch() {
  let src = "function f(cond: boolean) { let x: number; if (cond) { x = 1; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "cond"),
    store.primitive_ids().boolean,
  );
  let res = run_flow(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    &store,
    &initial,
  );
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
    src,
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
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "cond"),
    store.primitive_ids().boolean,
  );
  let res = run_flow(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    &store,
    &initial,
  );
  assert!(res.diagnostics().is_empty());
}

#[test]
fn loop_assignment_not_definite() {
  let src = "function f(cond: boolean) { let x: number; while (cond) { x = 1; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "cond"),
    store.primitive_ids().boolean,
  );
  let res = run_flow(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    &store,
    &initial,
  );
  assert_eq!(res.diagnostics().len(), 1);
  assert_eq!(
    res.diagnostics()[0].code.as_str(),
    codes::USE_BEFORE_ASSIGNMENT.as_str()
  );
}
