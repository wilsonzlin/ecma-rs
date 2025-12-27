use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{
  lower_file_with_diagnostics, Body, BodyId, DefKind, FileKind as HirFileKind, LowerResult,
  NameInterner,
};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::ts::locals::{bind_ts_locals, TsLocalSemantics};
use typecheck_ts::check::hir_body::{check_body_with_env, FlowBindings};
use types_ts_interned::{RelateCtx, TypeDisplay, TypeStore};

fn parse_and_lower_with_locals(source: &str) -> (LowerResult, TsLocalSemantics) {
  let mut ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let semantics = bind_ts_locals(&mut ast, FileId(0), true);
  let (lowered, _) = lower_file_with_diagnostics(FileId(0), HirFileKind::Ts, &ast);
  (lowered, semantics)
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
  let (lowered, semantics) = parse_and_lower_with_locals(src);
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let flow_bindings = FlowBindings::new(body, &semantics);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let expected = store.union(vec![prim.string, prim.null]);
  let param_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| flow_bindings.binding_for_pat(p.pat))
    .expect("param binding");
  initial.insert(param_binding, expected);

  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    Arc::clone(&store),
    &semantics,
    &initial,
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
  let (lowered, semantics) = parse_and_lower_with_locals(src);
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let flow_bindings = FlowBindings::new(body, &semantics);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let param_binding = body
    .function
    .as_ref()
    .and_then(|f| f.params.first())
    .and_then(|p| flow_bindings.binding_for_pat(p.pat))
    .expect("param binding");
  initial.insert(param_binding, store.union(vec![prim.string, prim.null]));

  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    Arc::clone(&store),
    &semantics,
    &initial,
    relate,
    None,
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
