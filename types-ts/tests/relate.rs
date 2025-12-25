use types_ts::*;

fn default_options() -> TypeOptions {
  TypeOptions {
    strict_null_checks: true,
    strict_function_types: true,
  }
}

#[test]
fn primitives_and_special_types() {
  let store = TypeStore::new();
  let ctx = RelateCtx::new(&store, default_options());

  assert!(ctx.is_assignable(store.string(), store.any()));
  assert!(ctx.is_assignable(store.any(), store.string()));
  assert!(ctx.is_assignable(store.number(), store.unknown()));
  assert!(!ctx.is_assignable(store.unknown(), store.number()));

  assert!(ctx.is_assignable(store.never(), store.string()));
  assert!(!ctx.is_assignable(store.string(), store.never()));

  assert!(!ctx.is_assignable(store.null(), store.string()));
  assert!(!ctx.is_assignable(store.undefined(), store.number()));

  let opts = TypeOptions {
    strict_null_checks: false,
    strict_function_types: true,
  };
  let relaxed = RelateCtx::new(&store, opts);
  assert!(relaxed.is_assignable(store.null(), store.string()));
  assert!(relaxed.is_assignable(store.string(), store.null()));
}

#[test]
fn unions_and_intersections() {
  let mut store = TypeStore::new();
  let num = store.number();
  let str_ty = store.string();
  let boolean = store.boolean();
  let num_or_str = store.union(vec![num, str_ty]);
  let num_str_bool = store.union(vec![num_or_str, boolean]);

  // intersection merge for objects
  let prop_a = Property {
    name: "a".into(),
    ty: str_ty,
    optional: false,
    readonly: false,
    is_method: false,
    visibility: MemberVisibility::Public,
    origin_id: None,
  };
  let prop_b = Property {
    name: "b".into(),
    ty: num,
    optional: false,
    readonly: false,
    is_method: false,
    visibility: MemberVisibility::Public,
    origin_id: None,
  };
  let obj_a = store.object(ObjectType::new(vec![prop_a.clone()], vec![]));
  let obj_b = store.object(ObjectType::new(vec![prop_b.clone()], vec![]));
  let intersection = store.intersection(vec![obj_a, obj_b]);
  let combined = store.object(ObjectType::new(vec![prop_a, prop_b], vec![]));

  let ctx = RelateCtx::new(&store, default_options());

  assert!(ctx.is_assignable(str_ty, num_or_str));
  assert!(!ctx.is_assignable(num_or_str, num));
  assert!(ctx.is_assignable(num_or_str, num_str_bool));
  assert!(ctx.is_assignable(intersection, combined));
}

#[test]
fn function_variance_and_methods() {
  let mut store = TypeStore::new();
  let num = store.number();
  let str_ty = store.string();
  let num_or_str = store.union(vec![num, str_ty]);

  let param_num = FnParam {
    name: None,
    ty: num,
    optional: false,
    rest: false,
  };
  let param_num_or_str = FnParam {
    name: None,
    ty: num_or_str,
    optional: false,
    rest: false,
  };

  let f_num = store.function(FunctionType {
    params: vec![param_num.clone()],
    ret: num,
    is_method: false,
    this_param: None,
  });
  let f_num_or_str = store.function(FunctionType {
    params: vec![param_num_or_str.clone()],
    ret: num,
    is_method: false,
    this_param: None,
  });

  // method exception even when strict
  let method_num = store.function(FunctionType {
    params: vec![param_num],
    ret: num,
    is_method: true,
    this_param: None,
  });
  let method_num_or_str = store.function(FunctionType {
    params: vec![param_num_or_str],
    ret: num,
    is_method: true,
    this_param: None,
  });
  let prop_method_n = Property {
    name: "m".into(),
    ty: method_num,
    optional: false,
    readonly: false,
    is_method: true,
    visibility: MemberVisibility::Public,
    origin_id: None,
  };
  let prop_method_ns = Property {
    name: "m".into(),
    ty: method_num_or_str,
    optional: false,
    readonly: false,
    is_method: true,
    visibility: MemberVisibility::Public,
    origin_id: None,
  };

  let obj_n = store.object(ObjectType::new(vec![prop_method_n], vec![]));
  let obj_ns = store.object(ObjectType::new(vec![prop_method_ns], vec![]));

  let ctx_strict = RelateCtx::new(&store, default_options());
  assert!(!ctx_strict.is_assignable(f_num, f_num_or_str));
  assert!(ctx_strict.is_assignable(f_num_or_str, f_num));

  let loose_opts = TypeOptions {
    strict_null_checks: true,
    strict_function_types: false,
  };
  let ctx_loose = RelateCtx::new(&store, loose_opts);
  assert!(ctx_loose.is_assignable(f_num, f_num_or_str));
  assert!(ctx_loose.is_assignable(f_num_or_str, f_num));

  assert!(ctx_strict.is_assignable(obj_n, obj_ns));
  assert!(ctx_strict.is_assignable(obj_ns, obj_n));
}

#[test]
fn index_signatures_cover_properties() {
  let mut store = TypeStore::new();
  let num = store.number();
  let prop = Property {
    name: "a".into(),
    ty: num,
    optional: false,
    readonly: false,
    is_method: false,
    visibility: MemberVisibility::Public,
    origin_id: None,
  };
  let src = store.object(ObjectType::new(vec![prop], vec![]));
  let target_index = IndexSignature {
    kind: IndexKind::String,
    ty: num,
    readonly: false,
  };
  let dst = store.object(ObjectType::new(vec![], vec![target_index]));

  let ctx = RelateCtx::new(&store, default_options());
  assert!(ctx.is_assignable(src, dst));
}

#[test]
fn cyclic_reference_terminates() {
  let mut store = TypeStore::new();
  let ref_id = TypeRefId(1);
  let tref = store.type_ref(ref_id);
  let cycle_union = store.union(vec![store.string(), tref]);

  struct Expand {
    ty: TypeId,
  }
  impl TypeExpander for Expand {
    fn expand_ref(&self, _store: &TypeStore, _reference: TypeRefId) -> Option<TypeId> {
      Some(self.ty)
    }
  }

  let hooks = RelateHooks {
    expander: None,
    is_same_origin_private_member: None,
  };
  // Need expander reference to live long enough
  let expander = Expand { ty: cycle_union };
  let hooks = RelateHooks {
    expander: Some(&expander),
    ..hooks
  };

  let ctx = RelateCtx::with_hooks(&store, default_options(), hooks);
  assert!(ctx.is_assignable(tref, tref));
  assert!(ctx.is_assignable(tref, store.string()));
  assert!(ctx.explain_assignable(tref, tref).result);
}
