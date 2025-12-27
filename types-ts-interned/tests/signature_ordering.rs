use std::cmp::Ordering;

use types_ts_interned::Param;
use types_ts_interned::Shape;
use types_ts_interned::Signature;
use types_ts_interned::SignatureId;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeParamDecl;
use types_ts_interned::TypeParamId;
use types_ts_interned::TypeStore;

fn signature_param_kinds(store: &TypeStore, signatures: &[SignatureId]) -> Vec<TypeKind> {
  signatures
    .iter()
    .map(|id| {
      let sig = store.signature(*id);
      let param = sig
        .params
        .first()
        .expect("signature should have at least one param");
      store.type_kind(param.ty)
    })
    .collect()
}

fn collect_overload_orders(
  intern_number_first: bool,
) -> (Vec<TypeKind>, Vec<TypeKind>, Vec<TypeKind>) {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let sig_number = Signature::new(
    vec![Param {
      name: None,
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.void,
  );
  let sig_string = Signature::new(
    vec![Param {
      name: None,
      ty: primitives.string,
      optional: false,
      rest: false,
    }],
    primitives.void,
  );

  let (id_number, id_string) = if intern_number_first {
    let id_number = store.intern_signature(sig_number.clone());
    let id_string = store.intern_signature(sig_string.clone());
    (id_number, id_string)
  } else {
    let id_string = store.intern_signature(sig_string.clone());
    let id_number = store.intern_signature(sig_number.clone());
    (id_number, id_string)
  };

  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![id_number, id_string],
  });

  let mut shape = Shape::new();
  shape.call_signatures = vec![id_number, id_string];
  shape.construct_signatures = vec![id_number, id_string];
  let shape_id = store.intern_shape(shape);

  let callable_order = match store.type_kind(callable) {
    TypeKind::Callable { overloads } => signature_param_kinds(&store, &overloads),
    other => panic!("expected callable, got {:?}", other),
  };

  let shape = store.shape(shape_id);
  let call_order = signature_param_kinds(&store, &shape.call_signatures);
  let construct_order = signature_param_kinds(&store, &shape.construct_signatures);

  (callable_order, call_order, construct_order)
}

#[test]
fn overloads_are_structurally_sorted() {
  let (callable_first, call_first, construct_first) = collect_overload_orders(true);
  let (callable_second, call_second, construct_second) = collect_overload_orders(false);

  let expected = vec![TypeKind::Number, TypeKind::String];

  assert_eq!(callable_first, expected);
  assert_eq!(call_first, expected);
  assert_eq!(construct_first, expected);

  assert_eq!(callable_first, callable_second);
  assert_eq!(call_first, call_second);
  assert_eq!(construct_first, construct_second);
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
