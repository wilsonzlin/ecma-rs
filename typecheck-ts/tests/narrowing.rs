use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, Body, BodyId, DefKind, LowerResult, NameId, NameInterner};
use typecheck_ts::check::hir_body::check_body_with_env;
use types_ts_interned::{
  NameId as TypeNameId, Param, PropData, PropKey, Property, Shape, Signature, TypeDisplay, TypeId,
  TypeKind, TypeStore,
};

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

#[test]
fn narrows_truthiness() {
  let src = "function f(x: string | null) { if (x) { return x; } else { return x; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.null]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "null");
}

#[test]
fn loose_nullish_comparison_narrows_non_nullish() {
  let src = "function f(x: string | null | undefined) { if (x != null) return x; return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.null, prim.undefined]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let ret_types = res.return_types();
  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "null | undefined");
}

#[test]
fn strict_undefined_comparison_narrows() {
  let src = "function f(x: string | undefined) { if (x === undefined) return x; return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.undefined]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let ret_types = res.return_types();
  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "undefined");
  assert_eq!(else_ty, "string");
}

#[test]
fn boolean_truthiness_splits_literals() {
  let src = "function f(flag: boolean) { if (flag) { return flag; } else { return flag; } }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "flag"),
    store.primitive_ids().boolean,
  );

  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );

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
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.number]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let ret_types = res.return_types();
  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn typeof_function_narrows_callables() {
  let src = "function pick(x) { if (typeof x === \"function\") { return x; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "pick");
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
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![callable, prim.number]),
  );

  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );

  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, callable_display);
  assert_eq!(else_ty, "number");
}

#[test]
fn narrows_discriminants() {
  let src = "function g(x: { kind: \"foo\", value: string } | { kind: \"bar\", value: number }) { if (x.kind === \"foo\") { return x.value; } else { return x.value; } }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "g");
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
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![foo_obj, bar_obj]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
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
  let lowered = lower_from_source(src).expect("lower");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let x_ty = store.union(vec![prim.string, prim.number]);
  initial.insert(name_id(lowered.names.as_ref(), "x"), x_ty);
  let guard_ty = predicate_callable(&store, x_ty, prim.string, false);
  initial.insert(name_id(lowered.names.as_ref(), "isStr"), guard_ty);

  let (body_id, body) = body_of(&lowered, &lowered.names, "test");
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
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
  let lowered = lower_from_source(src).expect("lower");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();

  let val_id = name_id(lowered.names.as_ref(), "val");
  initial.insert(val_id, store.union(vec![prim.string, prim.number]));

  let assert_name = name_id(lowered.names.as_ref(), "assertStr");
  let assert_ty = predicate_callable(
    &store,
    store.union(vec![prim.string, prim.number]),
    prim.string,
    true,
  );
  initial.insert(assert_name, assert_ty);

  let (body_id, body) = body_of(&lowered, &lowered.names, "useIt");
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
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
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "area");
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
    name_id(lowered.names.as_ref(), "shape"),
    store.union(vec![square, circle]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "number");
  assert_eq!(else_ty, "number");
}

#[test]
fn non_null_guard_allows_member_access() {
  let src = "function f(x: {a:number} | null) { if (x != null) return x.a; return 0 }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let obj = obj_type(&store, &[("a", prim.number)]);
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![obj, prim.null]),
  );

  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let ret_types = res.return_types();
  let then_ty = TypeDisplay::new(&store, ret_types[0]).to_string();
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "number");
  assert_eq!(else_ty, "0");
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
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.null]),
  );
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
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
  let lowered = lower_from_source(src).expect("lower");
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let (pick_body_id, pick_body) = body_of(&lowered, &lowered.names, "pick");
  let mut pick_env = HashMap::new();
  let pick_param = name_id(lowered.names.as_ref(), "x");
  let val_obj = obj_type(&store, &[("value", prim.string)]);
  let other_obj = obj_type(&store, &[("other", prim.number)]);
  pick_env.insert(pick_param, store.union(vec![val_obj, other_obj]));
  let res = check_body_with_env(
    pick_body_id,
    pick_body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &pick_env,
  );
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");

  let (obj_body_id, obj_body) = body_of(&lowered, &lowered.names, "onlyObjects");
  let mut obj_env = HashMap::new();
  obj_env.insert(
    name_id(lowered.names.as_ref(), "val"),
    store.union(vec![obj_type(&store, &[]), prim.number]),
  );
  let res = check_body_with_env(
    obj_body_id,
    obj_body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &obj_env,
  );
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
  let lowered = lower_from_source(src).expect("lower");
  let body = body_of(&lowered, &lowered.names, "onlyArrays");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let arr = store.intern_type(TypeKind::Array {
    ty: prim.string,
    readonly: false,
  });
  initial.insert(
    name_id(lowered.names.as_ref(), "val"),
    store.union(vec![arr, prim.number]),
  );

  let res = check_body_with_env(
    body.0,
    body.1,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
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
  let lowered = lower_from_source(src).expect("lower");
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
  initial.insert(name_id(lowered.names.as_ref(), "val"), val_ty);
  initial.insert(name_id(lowered.names.as_ref(), "isStr"), guard);

  let body = body_of(&lowered, &lowered.names, "pick");
  let res = check_body_with_env(
    body.0,
    body.1,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}
