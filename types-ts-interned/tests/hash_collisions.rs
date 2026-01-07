use types_ts_interned::{PropData, PropKey, Property, Shape, TypeOptions, TypeStore};

const SHAPE_DOMAIN: u64 = 0x7368_6170;

fn collide_shapes(raw: u128, domain: u64, salt: u64) -> u128 {
  if domain == SHAPE_DOMAIN && salt == 0 {
    0
  } else {
    raw
  }
}

fn shape_with_prop(store: &TypeStore, prop: &str) -> Shape {
  let primitives = store.primitive_ids();
  let mut shape = Shape::new();
  let prop = store.intern_name(prop);
  shape.properties.push(Property {
    key: PropKey::String(prop),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  shape
}

#[test]
#[cfg(not(feature = "strict-determinism"))]
fn collisions_are_rehashed_in_default_mode() {
  let store = TypeStore::with_options_and_fingerprint(TypeOptions::default(), collide_shapes);

  let shape_a = store.intern_shape(shape_with_prop(&store, "a"));
  assert_eq!(shape_a.0, 0);

  let shape_b = store.intern_shape(shape_with_prop(&store, "b"));
  assert_ne!(shape_a, shape_b);

  assert_eq!(store.shape(shape_a).properties.len(), 1);
  assert_eq!(store.shape(shape_b).properties.len(), 1);
}

#[test]
#[cfg(feature = "strict-determinism")]
#[should_panic(expected = "shape ID collision")]
fn collisions_panic_in_strict_mode() {
  let store = TypeStore::with_options_and_fingerprint(TypeOptions::default(), collide_shapes);

  let _ = store.intern_shape(shape_with_prop(&store, "a"));
  let _ = store.intern_shape(shape_with_prop(&store, "b"));
}
