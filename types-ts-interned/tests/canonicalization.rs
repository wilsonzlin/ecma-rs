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
