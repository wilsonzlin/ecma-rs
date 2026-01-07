use types_ts_interned::ObjectType;
use types_ts_interned::Param;
use types_ts_interned::Shape;
use types_ts_interned::Signature;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeStore;

#[test]
fn signature_interning_ignores_param_names() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");

  let sig_a = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(name_a),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.string,
  ));

  let sig_b = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(name_b),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.string,
  ));

  assert_eq!(sig_a, sig_b);

  // Parameter names should be canonicalized away while interning.
  let interned = store.signature(sig_a);
  assert_eq!(interned.params[0].name, None);
}

#[test]
fn types_differing_only_by_param_names_intern_to_same_id() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");

  let sig_a = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(name_a),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.string,
  ));

  let sig_b = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(name_b),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.string,
  ));

  let callable_a = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_a],
  });
  let callable_b = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_b],
  });
  assert_eq!(callable_a, callable_b);

  let mut shape_a = Shape::new();
  shape_a.call_signatures.push(sig_a);
  shape_a.construct_signatures.push(sig_a);
  let shape_a = store.intern_shape(shape_a);

  let mut shape_b = Shape::new();
  shape_b.call_signatures.push(sig_b);
  shape_b.construct_signatures.push(sig_b);
  let shape_b = store.intern_shape(shape_b);

  assert_eq!(shape_a, shape_b);

  let object_a = store.intern_object(ObjectType { shape: shape_a });
  let object_b = store.intern_object(ObjectType { shape: shape_b });
  let ty_a = store.intern_type(TypeKind::Object(object_a));
  let ty_b = store.intern_type(TypeKind::Object(object_b));
  assert_eq!(ty_a, ty_b);
}
