use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{
  lower_file_with_diagnostics, Body, BodyId, DefKind, FileKind as HirFileKind, LowerResult, NameId,
  NameInterner,
};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::ts::locals::{bind_ts_locals, TsLocalSemantics};
use typecheck_ts::check::caches::CheckerCaches;
use typecheck_ts::check::flow_bindings::FlowBindings;
use typecheck_ts::check::hir_body::{check_body_with_expander, refine_types_with_flow};
use typecheck_ts::lib_support::CacheOptions;
use types_ts_interned::{RelateCtx, RelateHooks, TypeDisplay, TypeStore};

fn parse_and_lower_with_locals(source: &str) -> (LowerResult, TsLocalSemantics) {
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let locals = bind_ts_locals(&mut ast, FileId(0), true);
  let (lowered, _) = lower_file_with_diagnostics(FileId(0), HirFileKind::Ts, &ast);
  (lowered, locals)
}

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
  lowered: &LowerResult,
  locals: &TsLocalSemantics,
  func: &str,
  file: FileId,
  src: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, types_ts_interned::TypeId>,
) -> typecheck_ts::BodyCheckResult {
  let (body_id, body) = body_of(lowered, &lowered.names, func);
  let flow_bindings = FlowBindings::new(body, locals);
  let caches = CheckerCaches::new(CacheOptions::default()).for_body();
  let hooks = RelateHooks::default();
  let relate = RelateCtx::with_hooks_and_cache(
    Arc::clone(&store),
    store.options(),
    hooks,
    caches.relation.clone(),
  );
  let ast = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let base_bindings: HashMap<String, types_ts_interned::TypeId> = initial
    .iter()
    .filter_map(|(name, ty)| lowered.names.resolve(*name).map(|name| (name.to_string(), *ty)))
    .collect();
  let base = check_body_with_expander(
    body_id,
    body,
    &lowered.names,
    file,
    &ast,
    Arc::clone(&store),
    &caches,
    &base_bindings,
    None,
    None,
    None,
  );
  refine_types_with_flow(
    body_id,
    body,
    &lowered.names,
    &flow_bindings,
    file,
    store,
    &base,
    initial,
    relate,
    None,
  )
}

#[test]
fn block_scoped_shadowing_does_not_poison_outer() {
  let src = r#"
function f(x: string | null) {
  if (x) {
    let x = 1;
  }
  return x;
}
"#;
  let (lowered, locals) = parse_and_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let expected = store.union(vec![prim.string, prim.null]);
  initial.insert(name_id(lowered.names.as_ref(), "x"), expected);

  let res = run_flow(
    &lowered,
    &locals,
    "f",
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );

  let ret_ty = res.return_types()[0];
  assert_eq!(
    TypeDisplay::new(&store, ret_ty).to_string(),
    TypeDisplay::new(&store, expected).to_string()
  );
}

#[test]
fn var_hoisting_reuses_function_scope_binding() {
  let src = r#"
function f(x: string | null) {
  if (x) {
    var x = 1;
  }
  return x;
}
"#;
  let (lowered, locals) = parse_and_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.null]),
  );

  let res = run_flow(
    &lowered,
    &locals,
    "f",
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );

  let ret_ty = res.return_types()[0];
  // Truthiness leaves `string` in the falsy branch (empty string), but the hoisted
  // assignment must still update the shared binding with `number`.
  let expected = store.union(vec![prim.number, prim.null, prim.string]);
  assert_eq!(
    TypeDisplay::new(&store, ret_ty).to_string(),
    TypeDisplay::new(&store, expected).to_string()
  );
}
