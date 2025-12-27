use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use typecheck_ts::check::widen::{
  widen_array_elements, widen_literal, widen_object_literal_props, widen_union_literals,
};
use types_ts_interned::{
  Indexer, ObjectType, PropData, PropKey, Property, Shape, TypeKind, TypeStore,
};

#[test]
fn widen_literal_to_primitives() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let num = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(1.0)));
  let str_lit = store.intern_type(TypeKind::StringLiteral(store.intern_name("lit")));
  let bool_lit = store.intern_type(TypeKind::BooleanLiteral(true));
  let big_lit = store.intern_type(TypeKind::BigIntLiteral(BigInt::from(5u8)));

  assert_eq!(widen_literal(&store, num), prim.number);
  assert_eq!(widen_literal(&store, str_lit), prim.string);
  assert_eq!(widen_literal(&store, bool_lit), prim.boolean);
  assert_eq!(widen_literal(&store, big_lit), prim.bigint);
  assert_eq!(widen_literal(&store, prim.number), prim.number);
}

#[test]
fn widen_union_and_arrays() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let num = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(2.0)));
  let str_lit = store.intern_type(TypeKind::StringLiteral(store.intern_name("x")));
  let union = store.union(vec![num, str_lit]);

  let widened_union = widen_union_literals(&store, union);
  let expected_union = store.union(vec![prim.number, prim.string]);
  assert_eq!(widened_union, expected_union);

  let array = store.intern_type(TypeKind::Array {
    ty: union,
    readonly: false,
  });
  let widened_array = widen_union_literals(&store, array);
  match store.type_kind(widened_array) {
    TypeKind::Array { ty, readonly } => {
      assert!(!readonly);
      assert_eq!(ty, expected_union);
    }
    other => panic!("expected array, got {:?}", other),
  }

  let readonly_array = store.intern_type(TypeKind::Array {
    ty: num,
    readonly: true,
  });
  match store.type_kind(widen_array_elements(&store, readonly_array)) {
    TypeKind::Array { ty, readonly } => {
      assert!(readonly);
      assert_eq!(ty, prim.number);
    }
    other => panic!("expected array, got {:?}", other),
  }
}

#[test]
fn widen_object_properties_and_indexers() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let num = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(3.0)));
  let str_lit = store.intern_type(TypeKind::StringLiteral(store.intern_name("value")));
  let bool_lit = store.intern_type(TypeKind::BooleanLiteral(false));

  let mut shape = Shape::new();
  shape.properties.push(Property {
    key: PropKey::String(store.intern_name("mutable")),
    data: PropData {
      ty: num,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  shape.properties.push(Property {
    key: PropKey::String(store.intern_name("readonly")),
    data: PropData {
      ty: str_lit,
      optional: false,
      readonly: true,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  shape.indexers.push(Indexer {
    key_type: prim.string,
    value_type: bool_lit,
    readonly: false,
  });

  let shape = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape });
  let obj_ty = store.intern_type(TypeKind::Object(obj));
  let widened = widen_object_literal_props(&store, obj_ty);

  let widened_shape = match store.type_kind(widened) {
    TypeKind::Object(obj) => store.shape(store.object(obj).shape),
    other => panic!("expected object, got {:?}", other),
  };

  let mut mutable_prop = None;
  let mut readonly_prop = None;
  for prop in widened_shape.properties.iter() {
    if let PropKey::String(name) = prop.key {
      match store.name(name).as_str() {
        "mutable" => mutable_prop = Some(prop.data.ty),
        "readonly" => readonly_prop = Some(prop.data.ty),
        _ => {}
      }
    }
  }

  let mutable_prop = mutable_prop.expect("mutable prop");
  assert!(matches!(store.type_kind(mutable_prop), TypeKind::Number));

  let readonly_prop = readonly_prop.expect("readonly prop");
  assert!(matches!(
    store.type_kind(readonly_prop),
    TypeKind::StringLiteral(_)
  ));

  let idx_ty = widened_shape.indexers.first().expect("indexer").value_type;
  assert!(matches!(store.type_kind(idx_ty), TypeKind::Boolean));
}
