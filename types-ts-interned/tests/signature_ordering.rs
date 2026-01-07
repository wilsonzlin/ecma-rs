use std::cmp::Ordering;

use types_ts_interned::Param;
use types_ts_interned::Shape;
use types_ts_interned::Signature;
use types_ts_interned::SignatureId;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeParamDecl;
use types_ts_interned::TypeParamId;
use types_ts_interned::TypeStore;

fn build_signature_set(store: &TypeStore) -> Vec<SignatureId> {
  let primitives = store.primitive_ids();
  let base_param = Param {
    name: None,
    ty: primitives.number,
    optional: false,
    rest: false,
  };

  let plain = store.intern_signature(Signature::new(vec![base_param.clone()], primitives.void));

  let mut with_this_sig = Signature::new(vec![base_param.clone()], primitives.void);
  with_this_sig.this_param = Some(primitives.string);
  let with_this = store.intern_signature(with_this_sig);

  let mut with_type_params_sig = Signature::new(vec![base_param], primitives.void);
  with_type_params_sig.type_params = vec![TypeParamDecl::new(TypeParamId(0))];
  let with_type_params = store.intern_signature(with_type_params_sig);

  vec![plain, with_this, with_type_params]
}

#[test]
fn callable_overload_sets_are_order_independent() {
  let store = TypeStore::new();
  let signatures = build_signature_set(&store);

  let mut expected = signatures.clone();
  expected.sort_by(|a, b| store.compare_signatures(*a, *b));

  let callable_a = store.intern_type(TypeKind::Callable {
    overloads: signatures.clone(),
  });
  let mut reversed = signatures.clone();
  reversed.reverse();
  let callable_b = store.intern_type(TypeKind::Callable {
    overloads: reversed,
  });

  assert_eq!(callable_a, callable_b);

  let overloads = match store.type_kind(callable_a) {
    TypeKind::Callable { overloads } => overloads,
    other => panic!("expected callable, got {:?}", other),
  };
  assert_eq!(overloads, expected);
}

#[test]
fn shape_signature_lists_are_order_independent() {
  let store = TypeStore::new();
  let signatures = build_signature_set(&store);

  let mut expected = signatures.clone();
  expected.sort_by(|a, b| store.compare_signatures(*a, *b));

  let mut shape_a = Shape::new();
  shape_a.call_signatures = signatures.clone();
  shape_a.construct_signatures = signatures.clone();
  let id_a = store.intern_shape(shape_a);

  let mut reversed = signatures.clone();
  reversed.reverse();
  let mut shape_b = Shape::new();
  shape_b.call_signatures = reversed.clone();
  shape_b.construct_signatures = reversed;
  let id_b = store.intern_shape(shape_b);

  assert_eq!(id_a, id_b);

  let shape = store.shape(id_a);
  assert_eq!(shape.call_signatures, expected);
  assert_eq!(shape.construct_signatures, expected);
}

#[test]
fn signature_ordering_accounts_for_this_and_type_params() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let base_param = Param {
    name: None,
    ty: primitives.number,
    optional: false,
    rest: false,
  };

  let without_this =
    store.intern_signature(Signature::new(vec![base_param.clone()], primitives.void));

  let mut with_this_sig = Signature::new(vec![base_param.clone()], primitives.void);
  with_this_sig.this_param = Some(primitives.string);
  let with_this = store.intern_signature(with_this_sig);

  let without_this_callable = store.intern_type(TypeKind::Callable {
    overloads: vec![without_this],
  });
  let with_this_callable = store.intern_type(TypeKind::Callable {
    overloads: vec![with_this],
  });

  assert_ne!(
    store.type_cmp(without_this_callable, with_this_callable),
    Ordering::Equal
  );

  let mut tp_a_sig = Signature::new(vec![base_param.clone()], primitives.void);
  tp_a_sig.type_params = vec![TypeParamDecl::new(TypeParamId(0))];
  let tp_a = store.intern_signature(tp_a_sig);

  let mut tp_b_sig = Signature::new(vec![base_param], primitives.void);
  tp_b_sig.type_params = vec![TypeParamDecl::new(TypeParamId(1))];
  let tp_b = store.intern_signature(tp_b_sig);

  let tp_a_callable = store.intern_type(TypeKind::Callable {
    overloads: vec![tp_a],
  });
  let tp_b_callable = store.intern_type(TypeKind::Callable {
    overloads: vec![tp_b],
  });

  let mut this_callables = vec![with_this_callable, without_this_callable];
  this_callables.sort_by(|a, b| store.type_cmp(*a, *b));
  assert_eq!(
    this_callables,
    vec![without_this_callable, with_this_callable]
  );

  let mut tp_callables = vec![tp_b_callable, tp_a_callable];
  tp_callables.sort_by(|a, b| store.type_cmp(*a, *b));
  assert_eq!(tp_callables, vec![tp_a_callable, tp_b_callable]);
  assert_ne!(
    store.type_cmp(tp_a_callable, tp_b_callable),
    Ordering::Equal
  );
}
