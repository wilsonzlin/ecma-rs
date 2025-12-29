use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameId, NameInterner};
use typecheck_ts::check::hir_body::check_body_with_env;
use types_ts_interned::{RelateCtx, TypeDisplay, TypeStore};

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
  _src: &str,
  store: &Arc<TypeStore>,
  initial: &HashMap<NameId, types_ts_interned::TypeId>,
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
  assert!(bindings.binding_for_name(name_id(lowered.names.as_ref(), "x")).is_some());

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
  let rendered: Vec<_> = returns
    .iter()
    .map(|ty| TypeDisplay::new(&store, *ty).to_string())
    .collect();
  let test_offset = src.find("typeof x === \"string\"").unwrap() as u32;
  let test_ty = res
    .expr_at(test_offset)
    .map(|(id, ty)| (id, TypeDisplay::new(&store, ty).to_string()));
  eprintln!("for_init_runs_once returns {:?}, test {:?}", rendered, test_ty);
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
  let rendered: Vec<_> = returns
    .iter()
    .map(|ty| TypeDisplay::new(&store, *ty).to_string())
    .collect();
  let test_offset = src.rfind("typeof x === \"string\"").unwrap() as u32;
  let test_ty = res
    .expr_at(test_offset)
    .map(|(id, ty)| (id, TypeDisplay::new(&store, ty).to_string()));
  eprintln!(
    "do_while_body_executes_before_test returns {:?}, test {:?}",
    rendered, test_ty
  );
  assert_eq!(TypeDisplay::new(&store, returns[0]).to_string(), "number");
  assert_eq!(TypeDisplay::new(&store, returns[1]).to_string(), "number");
}
