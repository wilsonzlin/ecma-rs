use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{
  lower_from_source, BinaryOp, Body, BodyId, DefKind, ExprId, ExprKind, LowerResult, NameId,
  NameInterner,
};
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
fn optional_chain_discriminant_narrows() {
  let src = r#"
function f(x: {kind:"a"}|{kind:"b"}|null) {
  if (x?.kind === "a") {
    return x.kind;
  }
  return x;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let kind_a = store.intern_type(TypeKind::StringLiteral(store.intern_name("a")));
  let kind_b = store.intern_type(TypeKind::StringLiteral(store.intern_name("b")));
  let a_obj = obj_type(&store, &[("kind", kind_a)]);
  let b_obj = obj_type(&store, &[("kind", kind_b)]);
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![a_obj, b_obj, prim.null]),
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
  let else_ty_expected = store.union(vec![b_obj, prim.null]);
  let else_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, TypeDisplay::new(&store, kind_a).to_string());
  assert_eq!(
    else_ty,
    TypeDisplay::new(&store, else_ty_expected).to_string()
  );
}

#[test]
fn optional_member_adds_undefined() {
  let src = r#"function g(x: {v: number} | null) { const y = x?.v; return y; }"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "g");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let obj = obj_type(&store, &[("v", prim.number)]);
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
  let expected = store.union(vec![prim.number, prim.undefined]);
  let ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  assert_eq!(ty, TypeDisplay::new(&store, expected).to_string());
}

#[test]
fn equality_between_refs_narrows_to_common_types() {
  let src = "function f(x: string | number, y: string) { if (x === y) { return x; } return x; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![prim.string, prim.number]),
  );
  initial.insert(name_id(lowered.names.as_ref(), "y"), prim.string);

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
  assert_eq!(else_ty, "number | string");
}

#[test]
fn equality_between_members_narrows_discriminants() {
  let src = r#"
function f(
  x: { kind: "foo", value: string } | { kind: "bar", value: number },
  y: { kind: "foo" },
) {
  if (x.kind === y.kind) {
    return x.kind;
  }
  return x.kind;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let foo = store.intern_type(TypeKind::StringLiteral(store.intern_name("foo")));
  let bar = store.intern_type(TypeKind::StringLiteral(store.intern_name("bar")));
  let foo_obj = obj_type(
    &store,
    &[("kind", foo), ("value", prim.string)],
  );
  let bar_obj = obj_type(
    &store,
    &[("kind", bar), ("value", prim.number)],
  );

  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![foo_obj, bar_obj]),
  );
  initial.insert(name_id(lowered.names.as_ref(), "y"), foo_obj);

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
  assert_eq!(then_ty, "\"foo\"");
  assert_eq!(else_ty, "\"bar\" | \"foo\"");
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
fn logical_and_applies_both_narrowings() {
  let src = r#"
function check(x: string | number) {
  if (x && typeof x === "string") {
    return x;
  }
  return x;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "check");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let x_ty = store.union(vec![prim.string, prim.number, prim.undefined]);
  initial.insert(name_id(lowered.names.as_ref(), "x"), x_ty);
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
  let after_ty = TypeDisplay::new(&store, ret_types[1]).to_string();
  assert_eq!(then_ty, "string");
  let expected_else =
    TypeDisplay::new(&store, store.union(vec![prim.number, prim.undefined])).to_string();
  assert_eq!(after_ty, expected_else);
}

#[test]
fn logical_or_keeps_truthy_conservative() {
  let src = r#"
function check(x: string | number) {
  if (x || typeof x === "string") {
    return x;
  }
  return x;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "check");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let x_ty = store.union(vec![prim.string, prim.number]);
  initial.insert(name_id(lowered.names.as_ref(), "x"), x_ty);
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
  let expected_truthy =
    TypeDisplay::new(&store, store.union(vec![prim.string, prim.number])).to_string();
  assert_eq!(then_ty, expected_truthy);
}

#[test]
fn nested_logical_composition_is_conservative() {
  let src = r#"
function check(x: string | number, y: boolean, z: boolean) {
  if ((x && y) || z) {
    return x;
  }
  return x;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "check");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let x_ty = store.union(vec![prim.string, prim.number]);
  initial.insert(name_id(lowered.names.as_ref(), "x"), x_ty);
  initial.insert(name_id(lowered.names.as_ref(), "y"), prim.boolean);
  initial.insert(name_id(lowered.names.as_ref(), "z"), prim.boolean);
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
  assert_eq!(ret_types[0], x_ty);
  assert_eq!(ret_types[1], x_ty);
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

#[test]
fn assignment_clears_previous_narrowing() {
  let src = r#"
function f(x: string | number) {
  if (typeof x === "string") {
    x;
    x = 1;
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
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, "number");
  assert_eq!(else_ty, "number");
}

#[test]
fn logical_and_assignment_preserves_truthiness() {
  let src = r#"
function f(x: string | null, y: string) {
  if (x &&= y) {
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
  initial.insert(name_id(lowered.names.as_ref(), "y"), prim.string);
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
fn nullish_assignment_removes_nullish() {
  let src = r#"
function f(x?: string, y: string) {
  x ??= y;
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
    store.union(vec![prim.string, prim.undefined]),
  );
  initial.insert(name_id(lowered.names.as_ref(), "y"), prim.string);
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
fn for_of_binds_element_type() {
  let src = r#"
function f(xs: string[]) {
  for (const x of xs) {
    return x;
  }
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let xs_ty = store.intern_type(TypeKind::Array {
    ty: prim.string,
    readonly: false,
  });
  initial.insert(name_id(lowered.names.as_ref(), "xs"), xs_ty);
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
fn for_in_uses_key_type() {
  let src = r#"
function g(obj: { a: number }) {
  for (const k in obj) {
    return k;
  }
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "g");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let obj_ty = obj_type(&store, &[("a", prim.number)]);
  initial.insert(name_id(lowered.names.as_ref(), "obj"), obj_ty);
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
fn nullish_coalescing_refines_result_type() {
  let src = r#"function f(x: string | null) { const y = x ?? ""; return y; }"#;
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

  let ret_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  assert_eq!(ret_ty, "string");
}

#[test]
fn nullish_assignment_updates_environment() {
  let src = r#"function g(x: string | null) { x ??= ""; return x; }"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "g");
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

  let ret_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  assert_eq!(ret_ty, "string");
}

#[test]
fn nullish_coalescing_narrows_member_base() {
  let src = r#"function h(x: string | null) { return (x ?? "").length; }"#;
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "h");
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

  let nullish_expr = body
    .exprs
    .iter()
    .enumerate()
    .find(|(_, expr)| matches!(expr.kind, ExprKind::Binary { op: BinaryOp::NullishCoalescing, .. }))
    .map(|(idx, _)| ExprId(idx as u32))
    .expect("nullish expression");

  let nullish_ty = res.expr_type(nullish_expr).unwrap();
  assert_eq!(TypeDisplay::new(&store, nullish_ty).to_string(), "string");
}

#[test]
fn overloaded_predicates_use_resolution() {
  let src = r#"
function isStr(x: string): x is string;
function isStr(x: number): x is number;
function isStr(x: any) { return true; }
function f(x: string | number) {
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

  let param_name = store.intern_name("x");
  let sig_string = store.intern_signature(Signature {
    params: vec![Param {
      name: Some(param_name),
      ty: prim.string,
      optional: false,
      rest: false,
    }],
    ret: store.intern_type(TypeKind::Predicate {
      parameter: Some(param_name),
      asserted: Some(prim.string),
      asserts: false,
    }),
    type_params: Vec::new(),
    this_param: None,
  });
  let sig_number = store.intern_signature(Signature {
    params: vec![Param {
      name: Some(param_name),
      ty: prim.number,
      optional: false,
      rest: false,
    }],
    ret: store.intern_type(TypeKind::Predicate {
      parameter: Some(param_name),
      asserted: Some(prim.number),
      asserts: false,
    }),
    type_params: Vec::new(),
    this_param: None,
  });
  let sig_any = store.intern_signature(Signature {
    params: vec![Param {
      name: Some(param_name),
      ty: prim.any,
      optional: false,
      rest: false,
    }],
    ret: prim.boolean,
    type_params: Vec::new(),
    this_param: None,
  });
  let guard = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_string, sig_number, sig_any],
  });
  initial.insert(name_id(lowered.names.as_ref(), "isStr"), guard);

  let (body_id, body) = body_of(&lowered, &lowered.names, "f");
  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );
  let expected = TypeDisplay::new(&store, x_ty).to_string();
  let then_ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let else_ty = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(then_ty, expected);
  assert_eq!(else_ty, expected);
}

#[test]
fn assertion_targets_named_argument() {
  let src = r#"
function assertStr(flag: number, candidate: string | number): asserts candidate is string {
  if (typeof candidate !== "string") {
    throw new Error("bad");
  }
}
function useIt(val: string | number) {
  assertStr(0, val);
  return val;
}
"#;
  let lowered = lower_from_source(src).expect("lower");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  let val_ty = store.union(vec![prim.string, prim.number]);
  initial.insert(name_id(lowered.names.as_ref(), "val"), val_ty);

  let candidate = store.intern_name("candidate");
  let guard = predicate_callable_with_params(
    &store,
    &[
      (Some(store.intern_name("flag")), prim.number),
      (Some(candidate), val_ty),
    ],
    prim.string,
    true,
    Some(candidate),
  );
  initial.insert(name_id(lowered.names.as_ref(), "assertStr"), guard);

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
fn try_finally_keeps_try_narrowing() {
  let src = r#"
function f(x: string | null) {
  try {
    if (x) return x;
  } finally {
    // no-op
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

  let first_return = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  let after_try = TypeDisplay::new(&store, res.return_types()[1]).to_string();
  assert_eq!(first_return, "string");
  assert_eq!(after_try, "null");
}

#[test]
fn try_catch_merges_assignments() {
  let src = r#"
function g(x: string) {
  try {
    x = 1 + 1;
  } catch {
  }
  return x;
}
"#;

  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "g");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let mut initial = HashMap::new();
  initial.insert(name_id(lowered.names.as_ref(), "x"), prim.string);

  let res = check_body_with_env(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    src,
    Arc::clone(&store),
    &initial,
  );

  let ret_ty = res.return_types()[0];
  let expected = store.union(vec![prim.string, prim.number]);
  assert_eq!(
    TypeDisplay::new(&store, ret_ty).to_string(),
    TypeDisplay::new(&store, expected).to_string()
  );
}

#[test]
fn finally_assignments_invalidate_narrowing() {
  let src = r#"
function h(x: string | null) {
  try {
    if (x) {
      x = x;
    }
  } finally {
    x = "done";
  }
  return x;
}
"#;

  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "h");
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

  let expected = prim.string;
  assert_eq!(
    TypeDisplay::new(&store, res.return_types()[0]).to_string(),
    TypeDisplay::new(&store, expected).to_string()
  );
}

#[test]
fn member_access_on_intersection_intersects_property_types() {
  let src = "function pick(x) { return x.value; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "pick");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let left = obj_type(&store, &[("value", prim.string)]);
  let right = obj_type(&store, &[("value", prim.number)]);
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.intersection(vec![left, right]),
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
  let ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  assert_eq!(ty, "number & string");
}

#[test]
fn member_access_on_union_unions_property_types() {
  let src = "function pick(x) { return x.value; }";
  let lowered = lower_from_source(src).expect("lower");
  let (body_id, body) = body_of(&lowered, &lowered.names, "pick");
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let left = obj_type(&store, &[("value", prim.string)]);
  let right = obj_type(&store, &[("value", prim.number)]);
  let mut initial = HashMap::new();
  initial.insert(
    name_id(lowered.names.as_ref(), "x"),
    store.union(vec![left, right]),
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
  let ty = TypeDisplay::new(&store, res.return_types()[0]).to_string();
  assert_eq!(ty, "number | string");
}
