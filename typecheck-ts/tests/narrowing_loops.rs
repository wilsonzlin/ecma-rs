use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameInterner};
use typecheck_ts::check::hir_body::{check_body_with_env, FlowBindingId, FlowBindings};
use types_ts_interned::{RelateCtx, TypeDisplay, TypeStore};

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
  let bindings = FlowBindings::from_body(body);

  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let param_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| bindings.binding_for_pat(p.pat))
    .expect("param binding");
  initial.insert(param_binding, store.union(vec![prim.string, prim.number]));

  let res = run_flow(body_id, body, &lowered.names, FileId(0), &store, &initial);
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
  let bindings = FlowBindings::from_body(body);

  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let param_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| bindings.binding_for_pat(p.pat))
    .expect("param binding");
  initial.insert(param_binding, store.union(vec![prim.string, prim.number]));

  let res = run_flow(body_id, body, &lowered.names, FileId(0), &store, &initial);
  let returns = res.return_types();
  assert_eq!(TypeDisplay::new(&store, returns[0]).to_string(), "number");
  assert_eq!(TypeDisplay::new(&store, returns[1]).to_string(), "number");
}
