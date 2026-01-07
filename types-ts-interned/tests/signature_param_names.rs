use types_ts_interned::{Param, Signature, TypeKind, TypeStore};

#[test]
fn signatures_ignore_parameter_names_when_interned() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let sig_a = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(store.intern_name("x")),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.void,
  ));
  let sig_b = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(store.intern_name("y")),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.void,
  ));

  assert_eq!(sig_a, sig_b);
  assert_eq!(store.signature(sig_a).params[0].name, None);
}

#[test]
fn callable_types_ignore_signature_parameter_names() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let sig_a = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(store.intern_name("x")),
      ty: primitives.boolean,
      optional: false,
      rest: false,
    }],
    primitives.number,
  ));
  let sig_b = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(store.intern_name("y")),
      ty: primitives.boolean,
      optional: false,
      rest: false,
    }],
    primitives.number,
  ));

  let callable_a = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_a],
  });
  let callable_b = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_b],
  });

  assert_eq!(callable_a, callable_b);
}
