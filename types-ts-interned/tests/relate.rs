use types_ts_interned::*;

fn default_options() -> TypeOptions {
  TypeOptions {
    strict_null_checks: true,
    strict_function_types: true,
  }
}

#[test]
fn primitives_and_special_types() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let ctx = RelateCtx::with_options(store.clone(), default_options());

  assert!(ctx.is_assignable(primitives.string, primitives.any));
  assert!(ctx.is_assignable(primitives.any, primitives.string));
  assert!(ctx.is_assignable(primitives.number, primitives.unknown));
  assert!(!ctx.is_assignable(primitives.unknown, primitives.number));

  assert!(ctx.is_assignable(primitives.never, primitives.string));
  assert!(!ctx.is_assignable(primitives.string, primitives.never));

  assert!(!ctx.is_assignable(primitives.null, primitives.string));
  assert!(!ctx.is_assignable(primitives.undefined, primitives.number));

  let relaxed = RelateCtx::with_options(
    store.clone(),
    TypeOptions {
      strict_null_checks: false,
      strict_function_types: true,
    },
  );
  assert!(relaxed.is_assignable(primitives.null, primitives.string));
  assert!(relaxed.is_assignable(primitives.string, primitives.null));
}

#[test]
fn unions_and_intersections() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let num_or_str = store.union(vec![primitives.number, primitives.string]);
  let num_str_bool = store.union(vec![num_or_str, primitives.boolean]);

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");

  let prop_a = Property {
    key: PropKey::String(name_a),
    data: PropData {
      ty: primitives.string,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      declared_on: None,
    },
  };
  let prop_b = Property {
    key: PropKey::String(name_b),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      declared_on: None,
    },
  };

  let shape_a = store.intern_shape(Shape {
    properties: vec![prop_a.clone()],
    call_signatures: vec![],
    construct_signatures: vec![],
    indexers: vec![],
  });
  let shape_b = store.intern_shape(Shape {
    properties: vec![prop_b.clone()],
    call_signatures: vec![],
    construct_signatures: vec![],
    indexers: vec![],
  });
  let obj_a = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_a }),
  ));
  let obj_b = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_b }),
  ));

  let intersection = store.intersection(vec![obj_a, obj_b]);
  let combined_shape = store.intern_shape(Shape {
    properties: vec![prop_a, prop_b],
    call_signatures: vec![],
    construct_signatures: vec![],
    indexers: vec![],
  });
  let combined = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: combined_shape,
  })));

  let ctx = RelateCtx::with_options(store.clone(), default_options());

  assert!(ctx.is_assignable(primitives.string, num_or_str));
  assert!(!ctx.is_assignable(num_or_str, primitives.number));
  assert!(ctx.is_assignable(num_or_str, num_str_bool));
  assert!(ctx.is_assignable(intersection, combined));
}

#[test]
fn function_variance_and_methods() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let num_or_str = store.union(vec![primitives.number, primitives.string]);

  let param_num = Param {
    name: None,
    ty: primitives.number,
    optional: false,
    rest: false,
  };
  let param_num_or_str = Param {
    name: None,
    ty: num_or_str,
    optional: false,
    rest: false,
  };

  let f_num = store.intern_type(TypeKind::Callable {
    overloads: vec![
      store.intern_signature(Signature::new(vec![param_num.clone()], primitives.number))
    ],
  });
  let f_num_or_str = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(Signature::new(
      vec![param_num_or_str.clone()],
      primitives.number,
    ))],
  });

  let method_num = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(Signature::new(vec![param_num], primitives.number))],
  });
  let method_num_or_str = store.intern_type(TypeKind::Callable {
    overloads: vec![
      store.intern_signature(Signature::new(vec![param_num_or_str], primitives.number))
    ],
  });

  let name_m = store.intern_name("m");
  let prop_method_n = Property {
    key: PropKey::String(name_m),
    data: PropData {
      ty: method_num,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: true,
      declared_on: None,
    },
  };
  let prop_method_ns = Property {
    key: PropKey::String(name_m),
    data: PropData {
      ty: method_num_or_str,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: true,
      declared_on: None,
    },
  };

  let obj_n = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: store.intern_shape(Shape {
      properties: vec![prop_method_n],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    }),
  })));
  let obj_ns = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: store.intern_shape(Shape {
      properties: vec![prop_method_ns],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    }),
  })));

  let ctx_strict = RelateCtx::with_options(store.clone(), default_options());
  assert!(!ctx_strict.is_assignable(f_num, f_num_or_str));
  assert!(ctx_strict.is_assignable(f_num_or_str, f_num));

  let loose_opts = TypeOptions {
    strict_null_checks: true,
    strict_function_types: false,
  };
  let ctx_loose = RelateCtx::with_options(store.clone(), loose_opts);
  assert!(ctx_loose.is_assignable(f_num, f_num_or_str));
  assert!(ctx_loose.is_assignable(f_num_or_str, f_num));

  assert!(ctx_strict.is_assignable(obj_n, obj_ns));
  assert!(ctx_strict.is_assignable(obj_ns, obj_n));
}

#[test]
fn index_signatures_cover_properties() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let name_a = store.intern_name("a");

  let src = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: store.intern_shape(Shape {
      properties: vec![Property {
        key: PropKey::String(name_a),
        data: PropData {
          ty: primitives.number,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          declared_on: None,
        },
      }],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    }),
  })));
  let dst = store.intern_type(TypeKind::Object(store.intern_object(ObjectType {
    shape: store.intern_shape(Shape {
      properties: vec![],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![Indexer {
        key_type: primitives.string,
        value_type: primitives.number,
        readonly: false,
      }],
    }),
  })));

  let ctx = RelateCtx::with_options(store.clone(), default_options());
  assert!(ctx.is_assignable(src, dst));
}

#[test]
fn cyclic_reference_terminates() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let ref_id = DefId(1);
  let tref = store.intern_type(TypeKind::Ref {
    def: ref_id,
    args: vec![],
  });
  let cycle_union = store.union(vec![primitives.string, tref]);

  struct Expand {
    ty: TypeId,
  }
  impl TypeExpander for Expand {
    fn expand_ref(&self, _store: &TypeStore, _def: DefId, _args: &[TypeId]) -> Option<TypeId> {
      Some(self.ty)
    }
  }

  let hooks = RelateHooks::default();
  let expander = Expand { ty: cycle_union };
  let hooks = RelateHooks {
    expander: Some(&expander),
    ..hooks
  };

  let ctx = RelateCtx::with_hooks(store.clone(), default_options(), hooks);
  assert!(ctx.is_assignable(tref, tref));
  assert!(ctx.is_assignable(tref, primitives.string));
  assert!(ctx.explain_assignable(tref, tref).result);
}
