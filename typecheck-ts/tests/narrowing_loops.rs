use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameId, NameInterner};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::check::caches::CheckerCaches;
use typecheck_ts::check::flow_bindings::FlowBindings;
use typecheck_ts::check::hir_body::{check_body_with_expander, refine_types_with_flow};
use typecheck_ts::lib_support::CacheOptions;
use types_ts_interned::{RelateCtx, RelateHooks, TypeDisplay, TypeStore};

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
fn for_init_runs_once() {
  let src = r#"
    function run(x: string | number) {
      for (x = "hi"; typeof x === "string"; x = 123) {
        return x;
      }
      return x;
    }
  "#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "run");

  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.number]),
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
  let returns = res.return_types();
  assert_eq!(TypeDisplay::new(&store, returns[0]).to_string(), "string");
  assert_eq!(TypeDisplay::new(&store, returns[1]).to_string(), "number");
}

#[test]
fn do_while_body_executes_before_test() {
  let src = r#"
    function run(x: string | number) {
      do {
        if (typeof x === "number") {
          return x;
        }
      } while (typeof x === "string");
      return x;
    }
  "#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "run");

  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.number]),
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
  let returns = res.return_types();
  assert_eq!(TypeDisplay::new(&store, returns[0]).to_string(), "number");
  assert_eq!(TypeDisplay::new(&store, returns[1]).to_string(), "number");
}
