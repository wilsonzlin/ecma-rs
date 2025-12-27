use types_ts_interned::{ObjectType, TypeId, TypeKind, TypeStore};

/// Widen a single literal type to its corresponding primitive, if applicable.
pub fn widen_literal(store: &TypeStore, ty: TypeId) -> TypeId {
  let prim = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::NumberLiteral(_) => prim.number,
    TypeKind::StringLiteral(_) => prim.string,
    TypeKind::BooleanLiteral(_) => prim.boolean,
    TypeKind::BigIntLiteral(_) => prim.bigint,
    _ => ty,
  }
}

/// Recursively widen literal members within unions, intersections, and arrays.
pub fn widen_union_literals(store: &TypeStore, ty: TypeId) -> TypeId {
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mapped: Vec<_> = members
        .into_iter()
        .map(|m| widen_union_literals(store, m))
        .collect();
      store.union(mapped)
    }
    TypeKind::Intersection(members) => {
      let mapped: Vec<_> = members
        .into_iter()
        .map(|m| widen_union_literals(store, m))
        .collect();
      store.intersection(mapped)
    }
    TypeKind::Array { ty, readonly } => {
      let widened = widen_union_literals(store, ty);
      store.intern_type(TypeKind::Array {
        ty: widened,
        readonly,
      })
    }
    _ => widen_literal(store, ty),
  }
}

/// Widen array element types by recursively widening literal members.
pub fn widen_array_elements(store: &TypeStore, ty: TypeId) -> TypeId {
  match store.type_kind(ty) {
    TypeKind::Array { ty, readonly } => {
      let widened = widen_union_literals(store, ty);
      store.intern_type(TypeKind::Array {
        ty: widened,
        readonly,
      })
    }
    _ => ty,
  }
}

/// Widen object literal property and indexer value types when they are mutable.
pub fn widen_object_literal_props(store: &TypeStore, ty: TypeId) -> TypeId {
  match store.type_kind(ty) {
    TypeKind::Object(obj_id) => {
      let obj = store.object(obj_id);
      let mut shape = store.shape(obj.shape);
      let mut changed = false;
      for prop in shape.properties.iter_mut() {
        if prop.data.readonly {
          continue;
        }
        let widened = widen_union_literals(store, prop.data.ty);
        if widened != prop.data.ty {
          prop.data.ty = widened;
          changed = true;
        }
      }
      for indexer in shape.indexers.iter_mut() {
        if indexer.readonly {
          continue;
        }
        let widened = widen_union_literals(store, indexer.value_type);
        if widened != indexer.value_type {
          indexer.value_type = widened;
          changed = true;
        }
      }
      if !changed {
        return ty;
      }
      let shape = store.intern_shape(shape);
      let obj = store.intern_object(ObjectType { shape });
      store.intern_type(TypeKind::Object(obj))
    }
    _ => ty,
  }
}
