use std::sync::Arc;

use types_ts_interned::{
  DefId, ExpandedType, ObjectType, Param, PropData, PropKey, Property, RelateCtx, Shape, Signature,
  TypeEvaluator, TypeExpander, TypeId, TypeKind, TypeOptions, TypeStore,
};

struct NoopExpander;

impl TypeExpander for NoopExpander {
  fn expand(&self, _store: &TypeStore, _def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    None
  }
}

fn callable(store: &Arc<TypeStore>, param: TypeId) -> TypeId {
  let sig = Signature::new(
    vec![Param {
      name: None,
      ty: param,
      optional: false,
      rest: false,
    }],
    store.primitive_ids().void,
  );
  let sig_id = store.intern_signature(sig);
  store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  })
}

fn method_object(store: &Arc<TypeStore>, param: TypeId, is_method: bool) -> TypeId {
  let callable = callable(store, param);
  let mut shape = Shape::new();
  shape.properties.push(Property {
    key: PropKey::String(store.intern_name("method")),
    data: PropData {
      ty: callable,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method,
      origin: None,
      declared_on: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}

fn optional_object(store: &Arc<TypeStore>, ty: TypeId) -> TypeId {
  let mut shape = Shape::new();
  shape.properties.push(Property {
    key: PropKey::String(store.intern_name("value")),
    data: PropData {
      ty,
      optional: true,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}

fn indexed_access(store: &Arc<TypeStore>, obj: TypeId, key: &str) -> TypeId {
  let access = store.intern_type(TypeKind::IndexedAccess {
    obj,
    index: store.intern_type(TypeKind::StringLiteral(store.intern_name(key))),
  });
  let mut evaluator = TypeEvaluator::new(store.clone(), &NoopExpander);
  evaluator.evaluate(access)
}

#[test]
fn strict_null_checks_toggle_assignability() {
  let strict_opts = TypeOptions::default();
  let loose_opts = TypeOptions {
    strict_null_checks: false,
    ..TypeOptions::default()
  };

  let strict_store = TypeStore::with_options(strict_opts);
  let loose_store = TypeStore::with_options(loose_opts);

  let strict_ctx = RelateCtx::new(strict_store.clone(), strict_opts);
  let loose_ctx = RelateCtx::new(loose_store.clone(), loose_opts);

  let strict_prim = strict_store.primitive_ids();
  let loose_prim = loose_store.primitive_ids();

  assert!(!strict_ctx.is_assignable(strict_prim.null, strict_prim.number));
  assert!(loose_ctx.is_assignable(loose_prim.null, loose_prim.number));
}

#[test]
fn strict_function_types_controls_parameter_variance() {
  let base_opts = TypeOptions::default();
  let loose_opts = TypeOptions {
    strict_function_types: false,
    ..base_opts
  };

  let strict_store = TypeStore::with_options(base_opts);
  let loose_store = TypeStore::with_options(loose_opts);
  let strict_ctx = RelateCtx::new(strict_store.clone(), base_opts);
  let loose_ctx = RelateCtx::new(loose_store.clone(), loose_opts);

  let strict_prim = strict_store.primitive_ids();
  let loose_prim = loose_store.primitive_ids();

  let wide = loose_store.union(vec![loose_prim.number, loose_prim.string]);
  let strict_wide = strict_store.union(vec![strict_prim.number, strict_prim.string]);

  let narrow_fn = callable(&strict_store, strict_prim.number);
  let wide_fn = callable(&strict_store, strict_wide);

  assert!(!strict_ctx.is_assignable(narrow_fn, wide_fn));
  assert!(loose_ctx.is_assignable(
    callable(&loose_store, loose_prim.number),
    callable(&loose_store, wide)
  ));

  // Methods remain bivariant even under strict function types.
  let strict_method_narrow = method_object(&strict_store, strict_prim.number, true);
  let strict_method_wide = method_object(&strict_store, strict_wide, true);
  assert!(strict_ctx.is_assignable(strict_method_narrow, strict_method_wide));

  let strict_func_narrow = method_object(&strict_store, strict_prim.number, false);
  let strict_func_wide = method_object(&strict_store, strict_wide, false);
  assert!(!strict_ctx.is_assignable(strict_func_narrow, strict_func_wide));
}

#[test]
fn exact_optional_property_types_preserves_declared_type() {
  let mut loose_opts = TypeOptions::default();
  loose_opts.exact_optional_property_types = false;
  let mut exact_opts = TypeOptions::default();
  exact_opts.exact_optional_property_types = true;

  let loose_store = TypeStore::with_options(loose_opts);
  let exact_store = TypeStore::with_options(exact_opts);

  let loose_obj = optional_object(&loose_store, loose_store.primitive_ids().number);
  let exact_obj = optional_object(&exact_store, exact_store.primitive_ids().number);

  let loose_access = indexed_access(&loose_store, loose_obj, "value");
  let exact_access = indexed_access(&exact_store, exact_obj, "value");

  let loose_kind = loose_store.type_kind(loose_access);
  let exact_kind = exact_store.type_kind(exact_access);

  match loose_kind {
    TypeKind::Union(members) => {
      assert!(members.contains(&loose_store.primitive_ids().undefined));
    }
    other => panic!("expected union for loose optional access, got {other:?}"),
  }

  assert_eq!(exact_kind, TypeKind::Number);
}

#[test]
fn no_unchecked_indexed_access_adds_undefined() {
  let mut opts = TypeOptions::default();
  opts.no_unchecked_indexed_access = true;
  let store = TypeStore::with_options(opts);
  let prim = store.primitive_ids();

  let required_obj = {
    let mut shape = Shape::new();
    shape.properties.push(Property {
      key: PropKey::String(store.intern_name("present")),
      data: PropData {
        ty: prim.number,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
    let shape_id = store.intern_shape(shape);
    let obj_id = store.intern_object(ObjectType { shape: shape_id });
    store.intern_type(TypeKind::Object(obj_id))
  };

  let access = indexed_access(&store, required_obj, "present");
  match store.type_kind(access) {
    TypeKind::Union(members) => {
      assert!(members.contains(&prim.undefined));
    }
    other => panic!("expected union including undefined, got {other:?}"),
  }
}

#[test]
#[should_panic]
fn relate_ctx_panics_on_mismatched_store_options() {
  let mut store_opts = TypeOptions::default();
  store_opts.no_unchecked_indexed_access = true;
  let store = TypeStore::with_options(store_opts);

  // RelateCtx must use the store's options; constructing it with mismatched
  // options should fail fast.
  let _ctx = RelateCtx::new(store.clone(), TypeOptions::default());
}
