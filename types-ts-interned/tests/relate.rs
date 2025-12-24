use types_ts_interned::Accessibility;
use types_ts_interned::DefId;
use types_ts_interned::Indexer;
use types_ts_interned::ObjectType;
use types_ts_interned::Param;
use types_ts_interned::PropData;
use types_ts_interned::PropKey;
use types_ts_interned::Property;
use types_ts_interned::RelateCtx;
use types_ts_interned::RelateHooks;
use types_ts_interned::RelateTypeExpander;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeOptions;
use types_ts_interned::TypeStore;
use types_ts_interned::{Shape, Signature};

fn default_options() -> TypeOptions {
  TypeOptions {
    strict_null_checks: true,
    strict_function_types: true,
    exact_optional_property_types: false,
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
  let ctx = RelateCtx::new(&store, default_options());

  assert!(ctx.is_assignable(primitives.string, primitives.any));
  assert!(ctx.is_assignable(primitives.any, primitives.string));
  assert!(ctx.is_assignable(primitives.number, primitives.unknown));
  assert!(!ctx.is_assignable(primitives.unknown, primitives.number));

  assert!(ctx.is_assignable(primitives.never, primitives.string));
  assert!(!ctx.is_assignable(primitives.string, primitives.never));

  assert!(!ctx.is_assignable(primitives.null, primitives.string));
  assert!(!ctx.is_assignable(primitives.undefined, primitives.number));

  let opts = TypeOptions {
    strict_null_checks: false,
    strict_function_types: true,
    exact_optional_property_types: false,
  };
  let relaxed = RelateCtx::new(&store, opts);
  assert!(relaxed.is_assignable(primitives.null, primitives.string));
  assert!(relaxed.is_assignable(primitives.string, primitives.null));
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

  let ctx = RelateCtx::new(&store, default_options());

  assert!(ctx.is_assignable(str_ty, num_or_str));
  assert!(!ctx.is_assignable(num_or_str, num));
  assert!(ctx.is_assignable(num_or_str, num_str_bool));
  assert!(ctx.is_assignable(intersection, combined));
}

#[test]
fn function_variance_and_methods() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let num = primitives.number;
  let str_ty = primitives.string;
  let num_or_str = store.union(vec![num, str_ty]);

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

  let f_num = callable(&store, vec![param_num.clone()], num);
  let f_num_or_str = callable(&store, vec![param_num_or_str.clone()], num);

  let method_num = callable(&store, vec![param_num], num);
  let method_num_or_str = callable(&store, vec![param_num_or_str], num);

  let prop_method_n = Property {
    key: PropKey::String(store.intern_name("m")),
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
    key: PropKey::String(store.intern_name("m")),
    data: PropData {
      ty: method_num_or_str,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: true,
      declared_on: None,
    },
  };

  let obj_n = object_type(
    &store,
    Shape {
      properties: vec![prop_method_n],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );
  let obj_ns = object_type(
    &store,
    Shape {
      properties: vec![prop_method_ns],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let ctx_strict = RelateCtx::new(&store, default_options());
  assert!(!ctx_strict.is_assignable(f_num, f_num_or_str));
  assert!(ctx_strict.is_assignable(f_num_or_str, f_num));

  let loose_opts = TypeOptions {
    strict_null_checks: true,
    strict_function_types: false,
    exact_optional_property_types: false,
  };
  let ctx_loose = RelateCtx::new(&store, loose_opts);
  assert!(ctx_loose.is_assignable(f_num, f_num_or_str));
  assert!(ctx_loose.is_assignable(f_num_or_str, f_num));

  assert!(ctx_strict.is_assignable(obj_n, obj_ns));
  assert!(ctx_strict.is_assignable(obj_ns, obj_n));
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

  let ctx = RelateCtx::new(&store, default_options());
  assert!(ctx.is_assignable(src, dst));
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

  let ctx_default = RelateCtx::new(&store, default_options());
  assert!(!ctx_default.is_assignable(src, dst));

  let hook = RelateHooks {
    expander: None,
    is_same_origin_private_member: Some(&|_, _| true),
  };
  let ctx_hook = RelateCtx::with_hooks(&store, default_options(), hook);
  assert!(ctx_hook.is_assignable(src, dst));
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

  let ctx = RelateCtx::with_hooks(&store, default_options(), hooks);
  assert!(ctx.is_assignable(tref, tref));
  assert!(ctx.is_assignable(tref, primitives.string));
  assert!(ctx.explain_assignable(tref, tref).result);
}
