use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{
  lower_file_with_diagnostics, Body, BodyId, DefKind, FileKind as HirFileKind, LowerResult, NameId,
  NameInterner,
};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::ts::locals::bind_ts_locals;
use typecheck_ts::check::flow_bindings::FlowBindings;
use typecheck_ts::check::hir_body::check_body_with_env_with_bindings;
use types_ts_interned::{RelateCtx, TypeDisplay, TypeStore};

fn parse_and_lower_with_locals(
  source: &str,
) -> (LowerResult, semantic_js::ts::locals::TsLocalSemantics) {
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let sem = bind_ts_locals(&mut ast, FileId(0), true);
  let (lowered, _) = lower_file_with_diagnostics(FileId(0), HirFileKind::Ts, &ast);
  (lowered, sem)
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
  let (lowered, sem) = parse_and_lower_with_locals(src);
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let bindings = FlowBindings::new(body, &sem);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let expected = store.union(vec![prim.string, prim.null]);
  initial.insert(name_id(lowered.names.as_ref(), "x"), expected);

  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  let res = check_body_with_env_with_bindings(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
    Some(&bindings),
    relate,
    None,
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
  let (lowered, sem) = parse_and_lower_with_locals(src);
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let bindings = FlowBindings::new(body, &sem);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.null]),
  );

  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  let res = check_body_with_env_with_bindings(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
    Some(&bindings),
    relate,
    None,
  );

  let ret_ty = res.return_types()[0];
  // The hoisted assignment updates the shared binding to include the number branch.
  let expected = store.union(vec![prim.number, prim.null]);
  assert_eq!(
    TypeDisplay::new(&store, ret_ty).to_string(),
    TypeDisplay::new(&store, expected).to_string()
  );
}
