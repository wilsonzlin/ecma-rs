use std::collections::HashMap;
use std::sync::Arc;

use ordered_float::OrderedFloat;
use typecheck_ts::check::infer::{
  infer_type_arguments_for_call, infer_type_arguments_from_contextual_signature,
};
use typecheck_ts::check::instantiate::{InstantiationCache, Substituter};
use typecheck_ts::check::overload::CallArgType;
use typecheck_ts::{FileKey, MemoryHost, Program, PropertyKey, TypeKindSummary};
use types_ts_interned::{
  CacheConfig, Param, RelateCtx, Signature, TypeId, TypeKind, TypeOptions, TypeParamDecl,
  TypeParamId, TypeStore,
};

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
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("x", t_type, &store)],
    ret: t_type,
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };

  let args = [CallArgType::new(primitives.number)];
  let result = infer_type_arguments_for_call(&store, &relate, &sig, &args, None);
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
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("a", t_type, &store), param("b", t_type, &store)],
    ret: t_type,
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };

  let args = [CallArgType::new(primitives.string), CallArgType::new(primitives.number)];
  let result = infer_type_arguments_for_call(&store, &relate, &sig, &args, None);
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
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let decl = TypeParamDecl {
    id: t_param,
    constraint: None,
    default: Some(primitives.string),
    variance: None,
    const_: false,
  };
  let sig = Signature {
    params: Vec::new(),
    ret: t_type,
    type_params: vec![decl.clone()],
    this_param: None,
  };
  let result = infer_type_arguments_for_call(&store, &relate, &sig, &[], None);
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.string));
}

#[test]
fn reports_constraint_violation() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let decl = TypeParamDecl {
    id: t_param,
    constraint: Some(primitives.number),
    default: None,
    variance: None,
    const_: false,
  };

  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![decl.clone()],
    this_param: None,
  };

  let args = [CallArgType::new(primitives.string)];
  let result = infer_type_arguments_for_call(&store, &relate, &sig, &args, None);
  assert_eq!(result.diagnostics.len(), 1);
  let diag = &result.diagnostics[0];
  assert_eq!(diag.param, t_param);
  assert_eq!(diag.constraint, primitives.number);
  assert_eq!(diag.actual, primitives.string);

  let expected = store.intersection(vec![primitives.string, primitives.number]);
  assert_eq!(result.substitutions.get(&t_param), Some(&expected));
}

#[test]
fn empty_object_constraint_allows_primitives_but_excludes_nullish() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));
  let empty_object = store.intern_type(TypeKind::EmptyObject);

  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![TypeParamDecl {
      id: t_param,
      constraint: Some(empty_object),
      default: None,
      variance: None,
      const_: false,
    }],
    this_param: None,
  };

  let ok_args = [CallArgType::new(primitives.number)];
  let ok = infer_type_arguments_for_call(&store, &relate, &sig, &ok_args, None);
  assert!(ok.diagnostics.is_empty());
  assert_eq!(ok.substitutions.get(&t_param), Some(&primitives.number));

  let bad_args = [CallArgType::new(primitives.null)];
  let result = infer_type_arguments_for_call(&store, &relate, &sig, &bad_args, None);
  assert_eq!(result.diagnostics.len(), 1);
  let diag = &result.diagnostics[0];
  assert_eq!(diag.param, t_param);
  assert_eq!(diag.constraint, empty_object);
  assert_eq!(diag.actual, primitives.null);

  let expected = store.intersection(vec![primitives.null, empty_object]);
  assert_eq!(result.substitutions.get(&t_param), Some(&expected));
}

#[test]
fn infers_from_function_argument_structure() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
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
    params: vec![
      param("items", item_array, &store),
      param("mapper", expected_callback, &store),
    ],
    ret: return_array,
    type_params: vec![TypeParamDecl::new(t_param), TypeParamDecl::new(u_param)],
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

  let call_args = [CallArgType::new(args[0]), CallArgType::new(args[1])];
  let result = infer_type_arguments_for_call(&store, &relate, &generic_sig, &call_args, None);
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.number));
  assert_eq!(result.substitutions.get(&u_param), Some(&primitives.string));
}

#[test]
fn infers_from_contravariant_function_parameter() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
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
    type_params: vec![TypeParamDecl::new(t_param)],
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

  let args = [CallArgType::new(actual_cb)];
  let result = infer_type_arguments_for_call(&store, &relate, &generic_sig, &args, None);
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
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };

  let mut subst = HashMap::new();
  subst.insert(t_param, primitives.boolean);

  let cache = InstantiationCache::default();
  let sig_id = store.intern_signature(sig.clone());
  let first = cache.instantiate_signature(&store, sig_id, &sig, &subst);
  let second = cache.instantiate_signature(&store, sig_id, &sig, &subst);
  assert_eq!(first, second);
}

#[test]
fn instantiation_cache_evictions_are_bounded_and_deterministic() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };

  let cache = InstantiationCache::with_config(CacheConfig {
    max_entries: 2,
    shard_count: 1,
  });
  let sig_id = store.intern_signature(sig.clone());

  for def in 0..16 {
    let mut subst = HashMap::new();
    subst.insert(
      t_param,
      store.intern_type(TypeKind::NumberLiteral(OrderedFloat(def as f64))),
    );
    let _ = cache.instantiate_signature(&store, sig_id, &sig, &subst);
  }

  let mut subst = HashMap::new();
  subst.insert(t_param, primitives.string);
  let first = cache.instantiate_signature(&store, sig_id, &sig, &subst);
  let second = cache.instantiate_signature(&store, sig_id, &sig, &subst);
  assert_eq!(first, second);

  let stats = cache.stats();
  assert!(stats.evictions > 0);
  assert!(stats.hits + stats.misses > 0);
}

#[test]
fn infers_from_contextual_signature_return_type() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let contextual_sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![TypeParamDecl::new(t_param)],
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
    &relate,
    &contextual_sig.type_params,
    &contextual_sig,
    &actual_sig,
  );
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.number));
}

#[test]
fn infers_from_contextual_signature_parameter() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let contextual_sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: primitives.void,
    type_params: vec![TypeParamDecl::new(t_param)],
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
    &relate,
    &contextual_sig.type_params,
    &contextual_sig,
    &actual_sig,
  );
  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.string));
}

#[test]
fn infers_from_contextual_return_in_call() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let t_param = TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));

  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };

  let args = [CallArgType::new(primitives.unknown)];
  let result = infer_type_arguments_for_call(&store, &relate, &sig, &args, Some(primitives.string));

  assert!(result.diagnostics.is_empty());
  assert_eq!(result.substitutions.get(&t_param), Some(&primitives.string));
}

#[test]
fn imported_type_alias_uses_source_definition() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(file_a.clone(), "export type Value = { value: number };");
  host.insert(
    file_b.clone(),
    r#"
import { Value } from "./a";
type Uses = Value;
"#,
  );
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b.clone()]);
  let file_a = program.file_id(&file_a).unwrap();
  let _value_def = program
    .definitions_in_file(file_a)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Value"))
    .unwrap();
  let file_b = program.file_id(&file_b).unwrap();
  let uses_def = program
    .definitions_in_file(file_b)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Uses"))
    .expect("Uses alias present");
  let ty = program.type_of_def(uses_def);
  let prop = program
    .property_type(ty, PropertyKey::String("value".into()))
    .expect("value property present");
  assert!(matches!(program.interned_type_kind(prop), TypeKind::Number));
}

#[test]
fn function_definition_exposes_signature() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  host.insert(
    file.clone(),
    "export function add(a: number, b: string): string { return a + b; }",
  );
  let program = Program::new(host, vec![file.clone()]);
  let file = program.file_id(&file).unwrap();
  let add_def = program
    .definitions_in_file(file)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("add"))
    .expect("add definition present");
  let ty = program.type_of_def(add_def);
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1);
  let sig = &sigs[0].signature;
  assert_eq!(sig.params.len(), 2);
  assert!(matches!(
    program.type_kind(sig.params[0].ty),
    TypeKindSummary::Number
  ));
  assert!(matches!(
    program.type_kind(sig.params[1].ty),
    TypeKindSummary::String
  ));
  assert!(matches!(
    program.type_kind(sig.ret),
    TypeKindSummary::String
  ));
}
