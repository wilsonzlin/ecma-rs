mod util;

use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{Body, BodyId};
use typecheck_ts::check::hir_body::{check_body_with_env, FlowBindingId, FlowBindings};
use types_ts_interned::{
  NameId as TypeNameId, Param, PropData, PropKey, Property, RelateCtx, Shape, Signature,
  TypeDisplay, TypeId, TypeKind, TypeStore,
};

const FILE_ID: FileId = FileId(0);
use crate::util::{binding_for_name, body_of, parse_lower_with_locals};

fn obj_type(store: &Arc<TypeStore>, props: &[(&str, TypeId)]) -> TypeId {
  let mut shape = Shape::new();
  for (name, ty) in props {
    shape.properties.push(Property {
      key: PropKey::String(store.intern_name(*name)),
      data: PropData {
        ty: *ty,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(types_ts_interned::ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}

fn predicate_callable(
  store: &Arc<TypeStore>,
  param_ty: TypeId,
  asserted: TypeId,
  asserts: bool,
) -> TypeId {
  predicate_callable_with_params(store, &[(None, param_ty)], asserted, asserts, None)
}

fn predicate_callable_with_params(
  store: &Arc<TypeStore>,
  params: &[(Option<TypeNameId>, TypeId)],
  asserted: TypeId,
  asserts: bool,
  predicate_param: Option<TypeNameId>,
) -> TypeId {
  let sig = Signature {
    params: params
      .iter()
      .map(|(name, ty)| Param {
        name: *name,
        ty: *ty,
        optional: false,
        rest: false,
      })
      .collect(),
    ret: store.intern_type(TypeKind::Predicate {
      parameter: predicate_param,
      asserted: Some(asserted),
      asserts,
    }),
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  })
}

fn param_binding(body: &Body, bindings: &FlowBindings, index: usize) -> FlowBindingId {
  let pat = body
    .function
    .as_ref()
    .expect("function body")
    .params
    .get(index)
    .expect("parameter exists")
    .pat;
  bindings.binding_for_pat(pat).expect("binding for parameter")
}

fn flow_context<'a>(
  parsed: &'a crate::util::Parsed,
  func: &str,
) -> (BodyId, &'a Body, FlowBindings) {
  let (body_id, body) = body_of(&parsed.lowered, &parsed.lowered.names, func);
  let bindings = FlowBindings::new(body, &parsed.semantics);
  (body_id, body, bindings)
}

fn run_flow(
  parsed: &crate::util::Parsed,
  body_id: BodyId,
  body: &Body,
  store: &Arc<TypeStore>,
  initial: &HashMap<FlowBindingId, TypeId>,
) -> typecheck_ts::BodyCheckResult {
  let relate = RelateCtx::new(Arc::clone(store), store.options());
  check_body_with_env(
    body_id,
    body,
    &parsed.lowered.names,
    FILE_ID,
    Arc::clone(store),
    &parsed.semantics,
    initial,
    relate,
    None,
  )
}

#[test]
fn narrows_truthiness() {
  let src = "function f(x: string | null) { if (x) { return x; } else { return x; } return x; }";
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let param_binding = param_binding(body, &bindings, 0);
  initial.insert(param_binding, store.union(vec![prim.string, prim.null]));
  for (idx, expr) in body.exprs.iter().enumerate() {
    if let hir_js::ExprKind::Ident(name) = &expr.kind {
      if parsed.lowered.names.resolve(*name) == Some("x") {
        let binding = bindings
          .binding_for_expr(hir_js::ExprId(idx as u32))
          .expect("binding for x");
        assert_eq!(binding, param_binding);
      }
    }
  }
  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "null");
}

#[test]
fn boolean_truthiness_splits_literals() {
  let src = "function f(flag: boolean) { if (flag) { return flag; } else { return flag; } }";
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "f");
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  initial.insert(
    param_binding(body, &bindings, 0),
    store.primitive_ids().boolean,
  );

  let res = run_flow(&parsed, body_id, body, &store, &initial);

  let true_ty =
    TypeDisplay::new(&store, store.intern_type(TypeKind::BooleanLiteral(true))).to_string();
  let false_ty =
    TypeDisplay::new(&store, store.intern_type(TypeKind::BooleanLiteral(false))).to_string();

  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, true_ty);
  assert_eq!(else_ty, false_ty);
}

#[test]
fn narrows_typeof_checks() {
  let src = "function f(x: string | number) { if (typeof x === \"string\") { return x; } else { return x; } }";
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    param_binding(body, &bindings, 0),
    store.union(vec![prim.string, prim.number]),
  );
  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let ret_types = res.return_types();
  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn typeof_function_narrows_callables() {
  let src = "function pick(x) { if (typeof x === \"function\") { return x; } return x; }";
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "pick");
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let sig = Signature {
    params: Vec::new(),
    ret: prim.number,
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  });
  let callable_display = TypeDisplay::new(&store, callable).to_string();

  let mut initial = HashMap::new();
  initial.insert(
    param_binding(body, &bindings, 0),
    store.union(vec![callable, prim.number]),
  );

  let res = run_flow(&parsed, body_id, body, &store, &initial);

  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, callable_display);
  assert_eq!(else_ty, "number");
}

#[test]
fn narrows_discriminants() {
  let src = "function g(x: { kind: \"foo\", value: string } | { kind: \"bar\", value: number }) { if (x.kind === \"foo\") { return x.value; } else { return x.value; } }";
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "g");
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  let foo = store.intern_type(TypeKind::StringLiteral(store.intern_name("foo")));
  let bar = store.intern_type(TypeKind::StringLiteral(store.intern_name("bar")));
  let foo_obj = obj_type(
    &store,
    &[("kind", foo), ("value", store.primitive_ids().string)],
  );
  let bar_obj = obj_type(
    &store,
    &[("kind", bar), ("value", store.primitive_ids().number)],
  );
  initial.insert(
    param_binding(body, &bindings, 0),
    store.union(vec![foo_obj, bar_obj]),
  );
  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let ret_types = res.return_types();
  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn user_defined_type_guards() {
  let src = r#"
function isStr(x: string | number): x is string {
  return typeof x === "string";
}
function test(x: string | number) {
  if (isStr(x)) {
    return x;
  }
  return x;
}
"#;
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let x_ty = store.union(vec![prim.string, prim.number]);
  let (body_id, body, bindings) = flow_context(&parsed, "test");
  initial.insert(param_binding(body, &bindings, 0), x_ty);
  let guard_ty = predicate_callable(&store, x_ty, prim.string, false);
  let guard_binding =
    binding_for_name(body, &bindings, &parsed.semantics, "isStr").expect("guard binding");
  initial.insert(guard_binding, guard_ty);
  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let ret_types = res.return_types();

  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();

  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn assertion_functions_narrow() {
  let src = r#"
function assertStr(x: string | number): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("bad");
  }
}
function useIt(val: string | number) {
  assertStr(val);
  return val;
}
"#;
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();

  let (body_id, body, bindings) = flow_context(&parsed, "useIt");
  let val_id = param_binding(body, &bindings, 0);
  initial.insert(val_id, store.union(vec![prim.string, prim.number]));

  let assert_name =
    binding_for_name(body, &bindings, &parsed.semantics, "assertStr").expect("assert binding");
  let assert_ty = predicate_callable(
    &store,
    store.union(vec![prim.string, prim.number]),
    prim.string,
    true,
  );
  initial.insert(assert_name, assert_ty);

  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  assert_eq!(ty, "string");
}

#[test]
fn switch_discriminant_narrows() {
  let src = r#"
function area(shape: { kind: "square", size: number } | { kind: "circle", radius: number }) {
  switch (shape.kind) {
    case "square":
      return shape.size;
    case "circle":
      return shape.radius;
  }
}
"#;
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "area");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let square = obj_type(
    &store,
    &[
      (
        "kind",
        store.intern_type(TypeKind::StringLiteral(store.intern_name("square"))),
      ),
      ("size", prim.number),
    ],
  );
  let circle = obj_type(
    &store,
    &[
      (
        "kind",
        store.intern_type(TypeKind::StringLiteral(store.intern_name("circle"))),
      ),
      ("radius", prim.number),
    ],
  );
  let mut initial = HashMap::new();
  initial.insert(
    param_binding(body, &bindings, 0),
    store.union(vec![square, circle]),
  );
  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "number");
  assert_eq!(else_ty, "number");
}

#[test]
fn short_circuit_preserves_narrowing() {
  let src = r#"
function f(x: string | null) {
  if (x && typeof x === "string") {
    return x;
  }
  return x;
}
"#;
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    param_binding(body, &bindings, 0),
    store.union(vec![prim.string, prim.null]),
  );
  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "null");
}

#[test]
fn in_and_instanceof_checks_narrow() {
  let src = r#"
function pick(x: { value: string } | { other: number }) {
  if ("value" in x) {
    return x.value;
  }
  return x.other;
}
function Box() {}
function onlyObjects(val: object | number) {
  if (val instanceof Box) {
    return val;
  }
  return val;
}
"#;
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let (pick_body_id, pick_body, pick_bindings) = flow_context(&parsed, "pick");
  let mut pick_env = HashMap::new();
  let pick_param = param_binding(pick_body, &pick_bindings, 0);
  let val_obj = obj_type(&store, &[("value", prim.string)]);
  let other_obj = obj_type(&store, &[("other", prim.number)]);
  pick_env.insert(pick_param, store.union(vec![val_obj, other_obj]));
  let res = run_flow(&parsed, pick_body_id, pick_body, &store, &pick_env);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");

  let (obj_body_id, obj_body, obj_bindings) = flow_context(&parsed, "onlyObjects");
  let mut obj_env = HashMap::new();
  obj_env.insert(
    param_binding(obj_body, &obj_bindings, 0),
    store.union(vec![obj_type(&store, &[]), prim.number]),
  );
  let res = run_flow(&parsed, obj_body_id, obj_body, &store, &obj_env);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "{}");
  assert_eq!(else_ty, "number");
}

#[test]
fn in_checks_cover_arrays() {
  let src = r#"
function onlyArrays(val: string[] | number) {
  if ("length" in val) {
    return val;
  }
  return val;
}
"#;
  let parsed = parse_lower_with_locals(src);
  let (body_id, body, bindings) = flow_context(&parsed, "onlyArrays");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let arr = store.intern_type(TypeKind::Array {
    ty: prim.string,
    readonly: false,
  });
  initial.insert(
    param_binding(body, &bindings, 0),
    store.union(vec![arr, prim.number]),
  );

  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, TypeDisplay::new(&store, arr).to_string());
  assert_eq!(else_ty, "number");
}

#[test]
fn predicate_targets_named_argument() {
  let src = r#"
function isStr(flag: number, candidate: string | number): candidate is string {
  return typeof candidate === "string";
}
function pick(val: string | number) {
  if (isStr(0, val)) {
    return val;
  }
  return val;
}
"#;
  let parsed = parse_lower_with_locals(src);
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let val_ty = store.union(vec![prim.string, prim.number]);
  let candidate = store.intern_name("candidate");
  let guard = predicate_callable_with_params(
    &store,
    &[
      (Some(store.intern_name("flag")), prim.number),
      (Some(candidate), val_ty),
    ],
    prim.string,
    false,
    Some(candidate),
  );
  let (body_id, body, bindings) = flow_context(&parsed, "pick");
  initial.insert(param_binding(body, &bindings, 0), val_ty);
  let guard_binding =
    binding_for_name(body, &bindings, &parsed.semantics, "isStr").expect("guard binding");
  initial.insert(guard_binding, guard);

  let res = run_flow(&parsed, body_id, body, &store, &initial);
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}
