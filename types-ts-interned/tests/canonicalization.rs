use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use types_ts_interned::Accessibility;
use types_ts_interned::PropData;
use types_ts_interned::PropKey;
use types_ts_interned::Property;
use types_ts_interned::Shape;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeStore;

#[test]
fn union_canonicalization_is_idempotent_and_sorted() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let union1 = store.union(vec![
    primitives.string,
    primitives.never,
    primitives.number,
    primitives.string,
  ]);
  let union2 = store.canon(union1);
  assert_eq!(union1, union2);

  let union3 = store.union(vec![primitives.number, primitives.string]);
  let union4 = store.union(vec![primitives.string, primitives.number]);
  assert_eq!(union1, union3);
  assert_eq!(union3, union4);

  // Ordering should be stable regardless of input order.
  let members = match store.type_kind(union1) {
    TypeKind::Union(m) => m,
    other => panic!("expected union, got {:?}", other),
  };
  assert_eq!(members, vec![primitives.number, primitives.string]);
}

#[test]
fn intersection_simplifies_special_members() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let inter1 = store.intersection(vec![primitives.string, primitives.unknown]);
  assert_eq!(inter1, primitives.string);

  let inter2 = store.intersection(vec![primitives.string, primitives.any]);
  assert_eq!(inter2, primitives.any);

  let inter3 = store.intersection(vec![primitives.never, primitives.string]);
  assert_eq!(inter3, primitives.never);
}

#[test]
fn union_absorbs_literals_and_unique_symbols() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let bool_lit = store.intern_type(TypeKind::BooleanLiteral(true));
  assert_eq!(store.union(vec![bool_lit]), bool_lit);
  assert_eq!(
    store.union(vec![primitives.boolean, bool_lit]),
    primitives.boolean
  );

  let num_lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(1.0)));
  assert_eq!(store.union(vec![num_lit]), num_lit);
  assert_eq!(
    store.union(vec![primitives.number, num_lit]),
    primitives.number
  );

  let str_lit = store.intern_type(TypeKind::StringLiteral(store.intern_name("a")));
  assert_eq!(store.union(vec![str_lit]), str_lit);
  assert_eq!(
    store.union(vec![primitives.string, str_lit]),
    primitives.string
  );

  let bigint_lit = store.intern_type(TypeKind::BigIntLiteral(BigInt::from(5u8)));
  assert_eq!(store.union(vec![bigint_lit]), bigint_lit);
  assert_eq!(
    store.union(vec![primitives.bigint, bigint_lit]),
    primitives.bigint
  );

  assert_eq!(
    store.union(vec![primitives.unique_symbol, primitives.symbol]),
    primitives.symbol
  );
}

#[test]
fn intersection_prefers_literals() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let bool_lit = store.intern_type(TypeKind::BooleanLiteral(false));
  assert_eq!(
    store.intersection(vec![primitives.boolean, bool_lit]),
    bool_lit
  );

  let str_lit = store.intern_type(TypeKind::StringLiteral(store.intern_name("b")));
  assert_eq!(
    store.intersection(vec![primitives.string, str_lit]),
    str_lit
  );

  let num_lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(2.0)));
  assert_eq!(
    store.intersection(vec![primitives.number, num_lit]),
    num_lit
  );

  let bigint_lit = store.intern_type(TypeKind::BigIntLiteral(BigInt::from(7u8)));
  assert_eq!(
    store.intersection(vec![primitives.bigint, bigint_lit]),
    bigint_lit
  );
}

#[test]
fn empty_intersection_is_unknown() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  assert_eq!(store.intersection(vec![]), primitives.unknown);
}

#[test]
fn shape_canonicalization_merges_duplicate_properties() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let name = store.intern_name("x");

  let shape = Shape {
    properties: vec![
      Property {
        key: PropKey::String(name),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: false,
          accessibility: None,
        },
      },
      Property {
        key: PropKey::String(name),
        data: PropData {
          ty: primitives.number,
          optional: true,
          readonly: true,
          accessibility: Some(Accessibility::Private),
        },
      },
    ],
    call_signatures: vec![],
    construct_signatures: vec![],
    indexers: vec![],
  };

  let shape_id = store.intern_shape(shape);
  let merged = store.shape(shape_id);
  assert_eq!(merged.properties.len(), 1);
  let prop = &merged.properties[0];
  assert_eq!(
    prop.data.ty,
    store.intersection(vec![primitives.string, primitives.number])
  );
  assert!(!prop.data.optional);
  assert!(prop.data.readonly);
  assert_eq!(prop.data.accessibility, Some(Accessibility::Private));
}

#[test]
fn canon_is_idempotent_on_nested_unions() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let nested = store.union(vec![
    store.union(vec![primitives.string, primitives.number]),
    store.union(vec![primitives.number, primitives.string]),
  ]);

  let once = store.canon(nested);
  let twice = store.canon(once);
  assert_eq!(once, twice);
}
