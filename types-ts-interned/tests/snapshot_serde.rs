use serde_json;
use types_ts_interned::{
  Accessibility, ObjectType, Param, PropData, PropKey, Property, Shape, Signature, TypeKind,
  TypeStore,
};

#[test]
fn type_store_snapshot_roundtrips_deterministically() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let sig = store.intern_signature(Signature::new(
    vec![Param {
      name: None,
      ty: prim.string,
      optional: false,
      rest: false,
    }],
    prim.number,
  ));

  let name = store.intern_name("prop");
  let mut shape = Shape::new();
  shape.properties.push(Property {
    key: PropKey::String(name),
    data: PropData {
      ty: prim.boolean,
      optional: false,
      readonly: false,
      accessibility: Some(Accessibility::Public),
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  let obj_ty = store.intern_type(TypeKind::Object(obj_id));
  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig],
  });
  let _union = store.intern_type(TypeKind::Union(vec![obj_ty, callable]));

  let snapshot = store.snapshot();
  let json_a = serde_json::to_string_pretty(&snapshot).expect("serialize");
  let json_b = serde_json::to_string_pretty(&store.snapshot()).expect("serialize again");
  assert_eq!(json_a, json_b, "snapshots should be deterministic");

  let restored = TypeStore::from_snapshot(snapshot);
  let json_roundtrip =
    serde_json::to_string_pretty(&restored.snapshot()).expect("serialize restored");
  assert_eq!(
    json_a, json_roundtrip,
    "restored snapshot should match original"
  );
}
