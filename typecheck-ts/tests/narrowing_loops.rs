mod util;

use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::Body;
use typecheck_ts::check::flow_bindings::{FlowBindingId, FlowBindings};
use typecheck_ts::check::hir_body::check_body_with_env;
use types_ts_interned::{RelateCtx, TypeDisplay, TypeId, TypeStore};

use crate::util::{binding_for_pat, body_of, parse_lower_with_locals};

const FILE_ID: FileId = FileId(0);

fn param_binding(parsed: &util::Parsed, body: &Body, index: usize) -> FlowBindingId {
  let pat = body
    .function
    .as_ref()
    .expect("function body")
    .params
    .get(index)
    .expect("parameter exists")
    .pat;
  binding_for_pat(body, &parsed.semantics, pat).expect("binding for parameter")
}

fn run_flow(
  parsed: &util::Parsed,
  func: &str,
  store: &Arc<TypeStore>,
  initial: &HashMap<FlowBindingId, TypeId>,
) -> typecheck_ts::BodyCheckResult {
  let (body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, func);
  let flow_bindings = FlowBindings::new(body, &parsed.semantics);
  let relate = RelateCtx::new(Arc::clone(store), store.options());
  check_body_with_env(
    body_id,
    body,
    &parsed.lowered.names,
    FILE_ID,
    Arc::clone(store),
    &flow_bindings,
    &parsed.semantics,
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
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let (_body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, "run");
  initial.insert(
    param_binding(&parsed, body, 0),
    store.union(vec![prim.string, prim.number]),
  );

  let res = run_flow(&parsed, "run", &store, &initial);
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
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let (_body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, "run");
  initial.insert(
    param_binding(&parsed, body, 0),
    store.union(vec![prim.string, prim.number]),
  );

  let res = run_flow(&parsed, "run", &store, &initial);
  let returns = res.return_types();
  assert_eq!(TypeDisplay::new(&store, returns[0]).to_string(), "number");
  assert_eq!(TypeDisplay::new(&store, returns[1]).to_string(), "number");
}
