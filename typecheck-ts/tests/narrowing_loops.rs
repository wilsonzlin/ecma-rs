mod util;

use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{Body, ExprId, NameId, PatId, PatKind};
use typecheck_ts::check::flow_bindings::FlowBindings;
use typecheck_ts::check::hir_body::{base_body_result, refine_types_with_flow};
use types_ts_interned::{RelateCtx, TypeDisplay, TypeId, TypeStore};

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
  let name_env = initial_name_env(body, &flow_bindings, initial);
  refine_types_with_flow(
    body_id,
    body,
    &parsed.lowered.names,
    &flow_bindings,
    &parsed.semantics,
    FILE_ID,
    Arc::clone(store),
    &base,
    &name_env,
    relate,
    None,
  )
}

fn initial_name_env(
  body: &Body,
  bindings: &FlowBindings,
  initial: &HashMap<NameId, TypeId>,
) -> HashMap<NameId, TypeId> {
  let mut env = HashMap::new();
  for (idx, expr) in body.exprs.iter().enumerate() {
    if let hir_js::ExprKind::Ident(name) = expr.kind {
      let expr_id = ExprId(idx as u32);
      if bindings.binding_for_expr(expr_id).is_some() {
        if let Some(ty) = initial.get(&name) {
          env.entry(name).or_insert(*ty);
        }
      }
    }
  }
  for (idx, pat) in body.pats.iter().enumerate() {
    if let PatKind::Ident(name) = pat.kind {
      let pat_id = PatId(idx as u32);
      if bindings.binding_for_pat(pat_id).is_some() {
        if let Some(ty) = initial.get(&name) {
          env.entry(name).or_insert(*ty);
        }
      }
    }
  }
  env
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
    param_name(body, 0),
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
    param_name(body, 0),
    store.union(vec![prim.string, prim.number]),
  );

  let res = run_flow(&parsed, "run", &store, &initial);
  let returns = res.return_types();
  assert_eq!(TypeDisplay::new(&store, returns[0]).to_string(), "number");
  assert_eq!(TypeDisplay::new(&store, returns[1]).to_string(), "number");
}
