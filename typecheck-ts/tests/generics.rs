use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::check::infer::{
  infer_type_arguments_for_call, infer_type_arguments_from_contextual_signature, TypeParamDecl,
};
use typecheck_ts::check::instantiate::{InstantiationCache, Substituter};
use types_ts_interned::{DefId, Param, Signature, TypeId, TypeKind, TypeParamId, TypeStore};

fn param(name: &str, ty: TypeId, store: &Arc<TypeStore>) -> Param {
  Param {
    name: Some(store.intern_name(name)),
    ty,
    optional: false,
    rest: false,
  }
}

#[test]
fn infers_identity_function() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("x", t_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  let result = infer_type_arguments_for_call(
    &store,
    &sig,
    &[TypeParamDecl::new(t_param)],
    &[primitives.number],
    None,
  );
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.number));

  let mut substituter = Substituter::new(Arc::clone(&store), result.substitutions);
  let instantiated_sig = substituter.substitute_signature(&sig);
  let resolved = store.signature(instantiated_sig);
  assert!(resolved.type_params.is_empty());
  assert_eq!(resolved.ret, primitives.number);
}

#[test]
fn infers_union_from_multiple_arguments() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("a", t_type, &store), param("b", t_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  let args = [primitives.string, primitives.number];
  let result = infer_type_arguments_for_call(
    &store,
    &sig,
    &[TypeParamDecl::new(t_param)],
    &args,
    None,
  );
  assert!(result.diagnostics.is_empty());
  let expected_union = store.union(vec![primitives.string, primitives.number]);
  assert_eq!(result.substitutions.get(&t_param), Some(&expected_union));

  let mut substituter = Substituter::new(Arc::clone(&store), result.substitutions);
  let instantiated_sig = substituter.substitute_signature(&sig);
  let resolved = store.signature(instantiated_sig);
  assert_eq!(resolved.ret, expected_union);
}

#[test]
fn uses_default_type_argument_when_not_inferred() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: Vec::new(),
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  let decl = TypeParamDecl {
    id: t_param,
    constraint: None,
    default: Some(primitives.string),
  };
  let result = infer_type_arguments_for_call(&store, &sig, &[decl], &[], None);
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.string));
}

#[test]
fn reports_constraint_violation() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  let decl = TypeParamDecl {
    id: t_param,
    constraint: Some(primitives.number),
    default: None,
  };

  let result =
    infer_type_arguments_for_call(&store, &sig, &[decl], &[primitives.string], None);
  assert_eq!(result.diagnostics.len(), 1);
  let diag = &result.diagnostics[0];
  assert_eq!(diag.param, t_param);
  assert!(diag.message.contains("does not satisfy constraint"));

  let expected = store.intersection(vec![primitives.string, primitives.number]);
  assert_eq!(result.substitutions.get(&t_param), Some(&expected));
}

#[test]
fn infers_from_function_argument_structure() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let u_param = TypeParamId(1);

  let t_type = store.intern_type(TypeKind::TypeParam(t_param));
  let u_type = store.intern_type(TypeKind::TypeParam(u_param));

  let item_array = store.intern_type(TypeKind::Array {
    ty: t_type,
    readonly: false,
  });

  let expected_callback_sig = Signature {
    params: vec![param("item", t_type, &store)],
    ret: u_type,
    type_params: Vec::new(),
    this_param: None,
  };
  let expected_callback = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(expected_callback_sig)],
  });

  let return_array = store.intern_type(TypeKind::Array {
    ty: u_type,
    readonly: false,
  });

  let generic_sig = Signature {
    params: vec![param("items", item_array, &store), param("mapper", expected_callback, &store)],
    ret: return_array,
    type_params: vec![t_param, u_param],
    this_param: None,
  };

  let inferred_callback_sig = Signature {
    params: vec![param("item", primitives.number, &store)],
    ret: primitives.string,
    type_params: Vec::new(),
    this_param: None,
  };
  let inferred_callback = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(inferred_callback_sig)],
  });
  let args = [
    store.intern_type(TypeKind::Array {
      ty: primitives.number,
      readonly: false,
    }),
    inferred_callback,
  ];

  let decls = vec![TypeParamDecl::new(t_param), TypeParamDecl::new(u_param)];
  let result = infer_type_arguments_for_call(&store, &generic_sig, &decls, &args, None);
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.number));
  assert_eq!(result.substitutions.get(&u_param), Some(&primitives.string));
}

#[test]
fn infers_from_contravariant_function_parameter() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let callback_sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: primitives.void,
    type_params: Vec::new(),
    this_param: None,
  };
  let callback_type = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(callback_sig)],
  });

  let generic_sig = Signature {
    params: vec![param("cb", callback_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  let actual_cb_sig = Signature {
    params: vec![param("value", primitives.number, &store)],
    ret: primitives.void,
    type_params: Vec::new(),
    this_param: None,
  };
  let actual_cb = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(actual_cb_sig)],
  });

  let result = infer_type_arguments_for_call(
    &store,
    &generic_sig,
    &[TypeParamDecl::new(t_param)],
    &[actual_cb],
    None,
  );
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.number));

  let mut substituter = Substituter::new(Arc::clone(&store), result.substitutions);
  let instantiated = substituter.substitute_signature(&generic_sig);
  let resolved = store.signature(instantiated);
  assert_eq!(resolved.ret, primitives.number);
}

#[test]
fn caches_instantiations_for_same_def() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  let mut subst = HashMap::new();
  subst.insert(t_param, primitives.boolean);

  let mut cache = InstantiationCache::default();
  let first = cache.instantiate_signature(&store, DefId(1), &sig, &subst);
  let second = cache.instantiate_signature(&store, DefId(1), &sig, &subst);
  assert_eq!(first, second);
}

#[test]
fn infers_from_contextual_signature_return_type() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let contextual_sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };

  // Actual lambda inferred to return number (body literal), no explicit param
  // type.
  let actual_sig = Signature {
    params: vec![param("value", primitives.unknown, &store)],
    ret: primitives.number,
    type_params: Vec::new(),
    this_param: None,
  };

  let result = infer_type_arguments_from_contextual_signature(
    &store,
    &contextual_sig,
    &[TypeParamDecl::new(t_param)],
    &actual_sig,
  );
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.number));
}

#[test]
fn infers_from_contextual_signature_parameter() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let contextual_sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: primitives.void,
    type_params: vec![t_param],
    this_param: None,
  };

  let actual_sig = Signature {
    params: vec![param("value", primitives.string, &store)],
    ret: primitives.void,
    type_params: Vec::new(),
    this_param: None,
  };

  let result = infer_type_arguments_from_contextual_signature(
    &store,
    &contextual_sig,
    &[TypeParamDecl::new(t_param)],
    &actual_sig,
  );
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.string));
}
