use types_ts_interned::Accessibility;
use types_ts_interned::DefId;
use types_ts_interned::Indexer;
use types_ts_interned::ObjectType;
use types_ts_interned::Param;
use types_ts_interned::PropData;
use types_ts_interned::PropKey;
use types_ts_interned::Property;
use types_ts_interned::ReasonNode;
use types_ts_interned::RelateCtx;
use types_ts_interned::RelateHooks;
use types_ts_interned::RelateTypeExpander;
use types_ts_interned::TupleElem;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeOptions;
use types_ts_interned::TypeParamId;
use types_ts_interned::TypeStore;
use types_ts_interned::{MappedModifier, MappedType, Shape, Signature};

fn default_options() -> TypeOptions {
  TypeOptions {
    strict_null_checks: true,
    strict_function_types: true,
    exact_optional_property_types: false,
    no_unchecked_indexed_access: false,
  }
}

fn object_type(store: &TypeStore, shape: Shape) -> types_ts_interned::TypeId {
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj))
}

fn callable(
  store: &TypeStore,
  params: Vec<Param>,
  ret: types_ts_interned::TypeId,
) -> types_ts_interned::TypeId {
  let sig = store.intern_signature(Signature::new(params, ret));
  store.intern_type(TypeKind::Callable {
    overloads: vec![sig],
  })
}

#[test]
fn primitives_and_special_types() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let ctx = RelateCtx::new(store.clone(), store.options());

  assert!(ctx.is_assignable(primitives.string, primitives.any));
  assert!(ctx.is_assignable(primitives.any, primitives.string));
  assert!(ctx.is_assignable(primitives.number, primitives.unknown));
  assert!(!ctx.is_assignable(primitives.unknown, primitives.number));

  assert!(ctx.is_assignable(primitives.never, primitives.string));
  assert!(!ctx.is_assignable(primitives.string, primitives.never));

  assert!(!ctx.is_assignable(primitives.null, primitives.string));
  assert!(!ctx.is_assignable(primitives.undefined, primitives.number));

  let relaxed_store = TypeStore::with_options(TypeOptions {
    strict_null_checks: false,
    ..default_options()
  });
  let relaxed_primitives = relaxed_store.primitive_ids();
  let relaxed = RelateCtx::new(relaxed_store.clone(), relaxed_store.options());
  assert!(relaxed.is_assignable(
    relaxed_primitives.null,
    relaxed_primitives.string
  ));
  assert!(relaxed.is_assignable(
    relaxed_primitives.string,
    relaxed_primitives.null
  ));
}

#[test]
fn type_params_treated_as_unknown() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let tp_a = store.intern_type(TypeKind::TypeParam(TypeParamId(0)));
  let tp_b = store.intern_type(TypeKind::TypeParam(TypeParamId(1)));
  let ctx = RelateCtx::new(store.clone(), default_options());

  assert!(ctx.is_assignable(primitives.number, tp_a));
  assert!(ctx.is_assignable(primitives.unknown, tp_a));
  assert!(ctx.is_assignable(primitives.any, tp_a));
  assert!(ctx.is_assignable(tp_a, primitives.unknown));
  assert!(ctx.is_assignable(tp_a, primitives.any));
  assert!(ctx.is_assignable(tp_a, tp_a));
  assert!(!ctx.is_assignable(tp_a, primitives.number));
  assert!(!ctx.is_assignable(tp_a, tp_b));
  assert!(!ctx.is_comparable(tp_a, primitives.unknown));
  assert!(ctx.is_comparable(tp_a, tp_a));
}

#[test]
fn strict_null_checks_propagate_through_objects() {
  let build_required_types = |store: &TypeStore| {
    let primitives = store.primitive_ids();
    let nullable_number = store.union(vec![primitives.number, primitives.null]);
    let required_nullable = object_type(
      store,
      Shape {
        properties: vec![Property {
          key: PropKey::String(store.intern_name("a")),
          data: PropData {
            ty: nullable_number,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        }],
        call_signatures: vec![],
        construct_signatures: vec![],
        indexers: vec![],
      },
    );
    let required_number = object_type(
      store,
      Shape {
        properties: vec![Property {
          key: PropKey::String(store.intern_name("a")),
          data: PropData {
            ty: primitives.number,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        }],
        call_signatures: vec![],
        construct_signatures: vec![],
        indexers: vec![],
      },
    );
    (required_nullable, required_number)
  };

  let strict_store = TypeStore::new();
  let (required_nullable, required_number) = build_required_types(&strict_store);
  let strict = RelateCtx::new(strict_store.clone(), strict_store.options());
  assert!(!strict.is_assignable(required_nullable, required_number));

  let loose_store = TypeStore::with_options(TypeOptions {
    strict_null_checks: false,
    ..default_options()
  });
  let (required_nullable, required_number) = build_required_types(&loose_store);
  let loose = RelateCtx::new(loose_store.clone(), loose_store.options());
  assert!(loose.is_assignable(required_nullable, required_number));
}

#[test]
fn unions_and_intersections() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let num = primitives.number;
  let str_ty = primitives.string;
  let boolean = primitives.boolean;
  let num_or_str = store.union(vec![num, str_ty]);
  let num_str_bool = store.union(vec![num_or_str, boolean]);

  let prop_a = Property {
    key: PropKey::String(store.intern_name("a")),
    data: PropData {
      ty: str_ty,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let prop_b = Property {
    key: PropKey::String(store.intern_name("b")),
    data: PropData {
      ty: num,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let obj_a = object_type(
    &store,
    Shape {
      properties: vec![prop_a.clone()],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let obj_b = object_type(
    &store,
    Shape {
      properties: vec![prop_b.clone()],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let intersection = store.intersection(vec![obj_a, obj_b]);
  let combined = object_type(
    &store,
    Shape {
      properties: vec![prop_a, prop_b],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx = RelateCtx::new(store.clone(), default_options());

  assert!(ctx.is_assignable(str_ty, num_or_str));
  assert!(!ctx.is_assignable(num_or_str, num));
  assert!(ctx.is_assignable(num_or_str, num_str_bool));
  assert!(ctx.is_assignable(intersection, combined));
}

#[test]
fn arrays_are_not_assignable_to_fixed_tuples() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let ctx = RelateCtx::new(store.clone(), default_options());

  let number_array = store.intern_type(TypeKind::Array {
    ty: primitives.number,
    readonly: false,
  });
  let fixed_tuple = store.intern_type(TypeKind::Tuple(vec![
    TupleElem {
      ty: primitives.number,
      optional: false,
      rest: false,
      readonly: false,
    },
    TupleElem {
      ty: primitives.number,
      optional: false,
      rest: false,
      readonly: false,
    },
    TupleElem {
      ty: primitives.number,
      optional: false,
      rest: false,
      readonly: false,
    },
  ]));
  assert!(!ctx.is_assignable(number_array, fixed_tuple));

  let rest_tuple = store.intern_type(TypeKind::Tuple(vec![TupleElem {
    ty: number_array,
    optional: false,
    rest: true,
    readonly: false,
  }]));
  assert!(ctx.is_assignable(number_array, rest_tuple));

  let readonly_array = store.intern_type(TypeKind::Array {
    ty: primitives.number,
    readonly: true,
  });
  assert!(!ctx.is_assignable(readonly_array, rest_tuple));
}

#[test]
fn function_variance_and_methods() {
  let strict_store = TypeStore::new();
  let primitives = strict_store.primitive_ids();
  let num = primitives.number;
  let str_ty = primitives.string;
  let num_or_str = strict_store.union(vec![num, str_ty]);

  let param_num = Param {
    name: None,
    ty: num,
    optional: false,
    rest: false,
  };
  let param_num_or_str = Param {
    name: None,
    ty: num_or_str,
    optional: false,
    rest: false,
  };

  let f_num = callable(&strict_store, vec![param_num.clone()], num);
  let f_num_or_str = callable(&strict_store, vec![param_num_or_str.clone()], num);

  let method_num = callable(&strict_store, vec![param_num], num);
  let method_num_or_str = callable(&strict_store, vec![param_num_or_str], num);

  let prop_method_n = Property {
    key: PropKey::String(strict_store.intern_name("m")),
    data: PropData {
      ty: method_num,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: true,
      origin: None,
      declared_on: None,
    },
  };
  let prop_method_ns = Property {
    key: PropKey::String(strict_store.intern_name("m")),
    data: PropData {
      ty: method_num_or_str,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: true,
      origin: None,
      declared_on: None,
    },
  };

  let obj_n = object_type(
    &strict_store,
    Shape {
      properties: vec![prop_method_n],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let obj_ns = object_type(
    &strict_store,
    Shape {
      properties: vec![prop_method_ns],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx_strict = RelateCtx::new(strict_store.clone(), strict_store.options());
  assert!(!ctx_strict.is_assignable(f_num, f_num_or_str));
  assert!(ctx_strict.is_assignable(f_num_or_str, f_num));

  let loose_store = TypeStore::with_options(TypeOptions {
    strict_function_types: false,
    ..default_options()
  });
  let loose_primitives = loose_store.primitive_ids();
  let loose_num = loose_primitives.number;
  let loose_num_or_str = loose_store.union(vec![loose_num, loose_primitives.string]);
  let loose_param_num = Param {
    name: None,
    ty: loose_num,
    optional: false,
    rest: false,
  };
  let loose_param_num_or_str = Param {
    name: None,
    ty: loose_num_or_str,
    optional: false,
    rest: false,
  };
  let loose_f_num = callable(&loose_store, vec![loose_param_num], loose_num);
  let loose_f_num_or_str = callable(&loose_store, vec![loose_param_num_or_str], loose_num);
  let ctx_loose = RelateCtx::new(loose_store.clone(), loose_store.options());
  assert!(ctx_loose.is_assignable(loose_f_num, loose_f_num_or_str));
  assert!(ctx_loose.is_assignable(loose_f_num_or_str, loose_f_num));

  assert!(ctx_strict.is_assignable(obj_n, obj_ns));
  assert!(ctx_strict.is_assignable(obj_ns, obj_n));
}

#[test]
fn function_properties_respect_strict_function_types() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let num = primitives.number;
  let num_or_str = store.union(vec![primitives.number, primitives.string]);

  let param_num = Param {
    name: None,
    ty: num,
    optional: false,
    rest: false,
  };
  let param_num_or_str = Param {
    name: None,
    ty: num_or_str,
    optional: false,
    rest: false,
  };

  let fn_narrow = callable(&store, vec![param_num.clone()], num);
  let fn_wide = callable(&store, vec![param_num_or_str.clone()], num);

  let prop_narrow = Property {
    key: PropKey::String(store.intern_name("f")),
    data: PropData {
      ty: fn_narrow,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let prop_wide = Property {
    key: PropKey::String(store.intern_name("f")),
    data: PropData {
      ty: fn_wide,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };

  let obj_narrow = object_type(
    &store,
    Shape {
      properties: vec![prop_narrow],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let obj_wide = object_type(
    &store,
    Shape {
      properties: vec![prop_wide],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx = RelateCtx::new(store.clone(), default_options());
  assert!(!ctx.is_assignable(obj_narrow, obj_wide));
  assert!(ctx.is_assignable(obj_wide, obj_narrow));
}

#[test]
fn index_signatures_cover_properties() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let num = primitives.number;
  let prop = Property {
    key: PropKey::String(store.intern_name("a")),
    data: PropData {
      ty: num,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let src = object_type(
    &store,
    Shape {
      properties: vec![prop],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let target_index = Indexer {
    key_type: primitives.string,
    value_type: num,
    readonly: false,
  };
  let dst = object_type(
    &store,
    Shape {
      properties: vec![],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![target_index],
    },
  );

  let ctx = RelateCtx::new(store.clone(), default_options());
  assert!(ctx.is_assignable(src, dst));
}

#[test]
fn no_unchecked_indexed_access_makes_indexers_optional() {
  let store = TypeStore::with_options(TypeOptions {
    no_unchecked_indexed_access: true,
    ..default_options()
  });
  let primitives = store.primitive_ids();
  let num = primitives.number;
  let target_prop = Property {
    key: PropKey::String(store.intern_name("a")),
    data: PropData {
      ty: num,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let src = object_type(
    &store,
    Shape {
      properties: vec![],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![Indexer {
        key_type: primitives.string,
        value_type: num,
        readonly: false,
      }],
    },
  );
  let dst = object_type(
    &store,
    Shape {
      properties: vec![target_prop],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx = RelateCtx::new(store.clone(), store.options());
  assert!(!ctx.is_assignable(src, dst));
}

#[test]
fn private_member_hook() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let private_prop = Property {
    key: PropKey::String(store.intern_name("x")),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Private),
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let extra_prop = Property {
    key: PropKey::String(store.intern_name("y")),
    data: PropData {
      ty: primitives.string,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let src = object_type(
    &store,
    Shape {
      properties: vec![private_prop.clone(), extra_prop],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let dst = object_type(
    &store,
    Shape {
      properties: vec![private_prop],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx_default = RelateCtx::new(store.clone(), default_options());
  assert!(!ctx_default.is_assignable(src, dst));

  let hook = RelateHooks {
    expander: None,
    is_same_origin_private_member: Some(&|_, _| true),
  };
  let ctx_hook = RelateCtx::with_hooks(store.clone(), default_options(), hook);
  assert!(ctx_hook.is_assignable(src, dst));
}

#[test]
fn private_members_with_same_origin_are_compatible_by_default() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let private_prop_src = Property {
    key: PropKey::String(store.intern_name("p")),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Private),
      is_method: false,
      origin: Some(1),
      declared_on: Some(DefId(1)),
    },
  };
  let private_prop_dst = Property {
    key: PropKey::String(store.intern_name("p")),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Private),
      is_method: false,
      origin: Some(1),
      declared_on: Some(DefId(1)),
    },
  };
  let src = object_type(
    &store,
    Shape {
      properties: vec![private_prop_src],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let dst = object_type(
    &store,
    Shape {
      properties: vec![private_prop_dst],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx = RelateCtx::new(store.clone(), default_options());
  assert!(ctx.is_assignable(src, dst));
}

#[test]
fn protected_members_require_same_origin() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let protected_prop_src = Property {
    key: PropKey::String(store.intern_name("p")),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Protected),
      is_method: false,
      origin: Some(1),
      declared_on: Some(DefId(1)),
    },
  };
  let protected_prop_dst = Property {
    key: PropKey::String(store.intern_name("p")),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Protected),
      is_method: false,
      origin: Some(2),
      declared_on: Some(DefId(2)),
    },
  };
  let src = object_type(
    &store,
    Shape {
      properties: vec![protected_prop_src],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let dst = object_type(
    &store,
    Shape {
      properties: vec![protected_prop_dst],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx = RelateCtx::new(store.clone(), default_options());
  assert!(!ctx.is_assignable(src, dst));
}

#[test]
fn derived_types_are_normalized_during_relation() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let base_obj = object_type(
    &store,
    Shape {
      properties: vec![Property {
        key: PropKey::String(store.intern_name("a")),
        data: PropData {
          ty: primitives.number,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      }],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let key_a = store.intern_type(TypeKind::StringLiteral(store.intern_name("a")));
  let keyof_obj = store.intern_type(TypeKind::KeyOf(base_obj));
  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: base_obj,
    index: key_a,
  });
  let conditional = store.intern_type(TypeKind::Conditional {
    check: primitives.string,
    extends: primitives.string,
    true_ty: primitives.number,
    false_ty: primitives.boolean,
    distributive: false,
  });
  let mapped = store.intern_type(TypeKind::Mapped(MappedType {
    param: TypeParamId(0),
    source: keyof_obj,
    value: primitives.string,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: None,
  }));
  let mapped_expected = object_type(
    &store,
    Shape {
      properties: vec![Property {
        key: PropKey::String(store.intern_name("a")),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      }],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx = RelateCtx::new(store.clone(), default_options());
  assert!(ctx.is_assignable(key_a, keyof_obj));
  assert!(!ctx.is_assignable(primitives.number, keyof_obj));

  assert!(ctx.is_assignable(primitives.number, indexed));
  assert!(!ctx.is_assignable(primitives.string, indexed));

  assert!(ctx.is_assignable(primitives.number, conditional));
  assert!(!ctx.is_assignable(primitives.boolean, conditional));

  assert!(ctx.is_assignable(mapped_expected, mapped));
  assert!(ctx.is_assignable(mapped, mapped_expected));
}

#[test]
fn conditional_normalization_uses_relation_ctx_hooks() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let private_prop = Property {
    key: PropKey::String(store.intern_name("x")),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Private),
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };

  let public_prop = Property {
    key: PropKey::String(store.intern_name("y")),
    data: PropData {
      ty: primitives.string,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };

  let check_obj = object_type(
    &store,
    Shape {
      properties: vec![private_prop.clone(), public_prop],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let extends_obj = object_type(
    &store,
    Shape {
      properties: vec![private_prop],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  assert_ne!(check_obj, extends_obj);

  let conditional = store.intern_type(TypeKind::Conditional {
    check: check_obj,
    extends: extends_obj,
    true_ty: primitives.number,
    false_ty: primitives.boolean,
    distributive: false,
  });

  // Without the hook, private members are incompatible, so the conditional
  // reduces to the false branch.
  let ctx_default = RelateCtx::new(store.clone(), default_options());
  assert!(ctx_default.is_assignable(primitives.boolean, conditional));
  assert!(!ctx_default.is_assignable(primitives.number, conditional));

  // With the hook enabled, private members are treated as same-origin, so the
  // conditional reduces to the true branch.
  let hook = RelateHooks {
    expander: None,
    is_same_origin_private_member: Some(&|_, _| true),
  };
  let ctx_hook = RelateCtx::with_hooks(store.clone(), default_options(), hook);
  assert!(ctx_hook.is_assignable(primitives.number, conditional));
  assert!(!ctx_hook.is_assignable(primitives.boolean, conditional));
}

#[test]
fn conditional_normalization_uses_structural_assignability() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let src = object_type(
    &store,
    Shape {
      properties: vec![
        Property {
          key: PropKey::String(store.intern_name("a")),
          data: PropData {
            ty: primitives.number,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
        Property {
          key: PropKey::String(store.intern_name("b")),
          data: PropData {
            ty: primitives.string,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
      ],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let dst = object_type(
    &store,
    Shape {
      properties: vec![Property {
        key: PropKey::String(store.intern_name("a")),
        data: PropData {
          ty: primitives.number,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      }],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let conditional = store.intern_type(TypeKind::Conditional {
    check: src,
    extends: dst,
    true_ty: primitives.number,
    false_ty: primitives.boolean,
    distributive: false,
  });

  let ctx = RelateCtx::new(store.clone(), store.options());
  assert!(ctx.is_assignable(primitives.number, conditional));
  assert!(!ctx.is_assignable(primitives.boolean, conditional));
}

#[test]
fn cyclic_reference_terminates() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let tref = store.intern_type(TypeKind::Ref {
    def: DefId(1),
    args: vec![],
  });
  let cycle_union = store.union(vec![primitives.string, tref]);

  struct Expand {
    ty: types_ts_interned::TypeId,
  }
  impl RelateTypeExpander for Expand {
    fn expand_ref(
      &self,
      _store: &TypeStore,
      _def: DefId,
      _args: &[types_ts_interned::TypeId],
    ) -> Option<types_ts_interned::TypeId> {
      Some(self.ty)
    }
  }

  let expander = Expand { ty: cycle_union };
  let hooks = RelateHooks {
    expander: Some(&expander),
    is_same_origin_private_member: None,
  };

  let ctx = RelateCtx::with_hooks(store.clone(), default_options(), hooks);
  assert!(ctx.is_assignable(tref, tref));
  assert!(ctx.is_assignable(tref, primitives.string));
  assert!(ctx.explain_assignable(tref, tref).result);
}

#[test]
fn explain_assignable_reason_nodes_only_reference_interned_type_ids() {
  fn walk_reason(store: &TypeStore, node: &ReasonNode) {
    assert!(
      store.contains_type_id(node.src),
      "uninterned reason src TypeId: {:?}",
      node.src
    );
    assert!(
      store.contains_type_id(node.dst),
      "uninterned reason dst TypeId: {:?}",
      node.dst
    );
    for child in &node.children {
      walk_reason(store, child);
    }
  }

  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let ctx = RelateCtx::new(store.clone(), default_options());

  let num = primitives.number;
  let num_or_str = store.union(vec![primitives.number, primitives.string]);

  let src = callable(
    &store,
    vec![Param {
      name: None,
      ty: num_or_str,
      optional: false,
      rest: false,
    }],
    num,
  );
  let dst = callable(
    &store,
    vec![Param {
      name: None,
      ty: num,
      optional: false,
      rest: false,
    }],
    num,
  );

  let result = ctx.explain_assignable(src, dst);
  assert!(result.result);
  let reason = result.reason.expect("expected reason tree");
  walk_reason(&store, &reason);
}

#[test]
fn cyclic_reference_conditional_normalization_terminates() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let tref = store.intern_type(TypeKind::Ref {
    def: DefId(1),
    args: vec![],
  });

  let src = object_type(
    &store,
    Shape {
      properties: vec![
        Property {
          key: PropKey::String(store.intern_name("a")),
          data: PropData {
            ty: primitives.number,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
        Property {
          key: PropKey::String(store.intern_name("b")),
          data: PropData {
            ty: primitives.string,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
      ],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let dst = object_type(
    &store,
    Shape {
      properties: vec![Property {
        key: PropKey::String(store.intern_name("a")),
        data: PropData {
          ty: primitives.number,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      }],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  // `tref` expands to a conditional type whose true branch is a union containing
  // `tref` again. The relation engine must normalize through this cycle without
  // overflowing the stack.
  let cycle_union = store.union(vec![primitives.number, tref]);
  let conditional = store.intern_type(TypeKind::Conditional {
    check: src,
    extends: dst,
    true_ty: cycle_union,
    false_ty: primitives.boolean,
    distributive: false,
  });

  struct Expand {
    ty: types_ts_interned::TypeId,
  }
  impl RelateTypeExpander for Expand {
    fn expand_ref(
      &self,
      _store: &TypeStore,
      _def: DefId,
      _args: &[types_ts_interned::TypeId],
    ) -> Option<types_ts_interned::TypeId> {
      Some(self.ty)
    }
  }

  let expander = Expand { ty: conditional };
  let hooks = RelateHooks {
    expander: Some(&expander),
    is_same_origin_private_member: None,
  };

  let ctx = RelateCtx::with_hooks(store.clone(), store.options(), hooks);
  assert!(ctx.is_assignable(primitives.number, tref));
}
