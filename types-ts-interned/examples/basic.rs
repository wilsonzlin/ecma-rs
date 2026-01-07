use std::sync::Arc;

use types_ts_interned::{
  ObjectType, Param, PropData, PropKey, Property, RelateCtx, Shape, Signature, TypeDisplay,
  TypeKind, TypeStore,
};

fn main() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let name_x = store.intern_name("x");
  let name_y = store.intern_name("y");

  let prop_x = Property {
    key: PropKey::String(name_x),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };
  let prop_y = Property {
    key: PropKey::String(name_y),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  };

  // `{ x: number }`
  let shape_a = Shape {
    properties: vec![prop_x.clone()],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  };
  let shape_a = store.intern_shape(shape_a);
  let obj_a = store.intern_object(ObjectType { shape: shape_a });
  let ty_a = store.intern_type(TypeKind::Object(obj_a));

  // `{ x: number, y: number }` (properties deliberately inserted out-of-order; the store canonicalizes them)
  let shape_b = Shape {
    properties: vec![prop_y, prop_x],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  };
  let shape_b = store.intern_shape(shape_b);
  let obj_b = store.intern_object(ObjectType { shape: shape_b });
  let ty_b = store.intern_type(TypeKind::Object(obj_b));

  println!("A = {}", TypeDisplay::new(store.as_ref(), ty_a));
  println!("B = {}", TypeDisplay::new(store.as_ref(), ty_b));

  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  println!("B assignable to A: {}", relate.is_assignable(ty_b, ty_a));
  println!("A assignable to B: {}", relate.is_assignable(ty_a, ty_b));

  let union = store.union(vec![primitives.string, primitives.number, primitives.string]);
  println!("union = {}", TypeDisplay::new(store.as_ref(), union));

  let sig = Signature::new(
    vec![
      Param {
        name: None,
        ty: primitives.number,
        optional: false,
        rest: false,
      },
      Param {
        name: None,
        ty: primitives.number,
        optional: false,
        rest: false,
      },
    ],
    primitives.number,
  );
  let sig = store.intern_signature(sig);
  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig],
  });
  println!("callable = {}", TypeDisplay::new(store.as_ref(), callable));

  println!(
    "callable assignable to unknown: {}",
    relate.is_assignable(callable, primitives.unknown)
  );
  println!(
    "unknown assignable to number: {}",
    relate.is_assignable(primitives.unknown, primitives.number)
  );
}

