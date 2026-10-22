use super::*;
use std::collections::HashSet;

pub(in super::super) fn lookup_interned_property_type(
  store: &tti::TypeStore,
  expander: Option<&dyn tti::RelateTypeExpander>,
  ty: tti::TypeId,
  name: &str,
) -> Option<tti::TypeId> {
  let mut seen = HashSet::new();
  lookup_interned_property_type_inner(store, expander, ty, name, &mut seen)
}

fn lookup_interned_property_type_inner(
  store: &tti::TypeStore,
  expander: Option<&dyn tti::RelateTypeExpander>,
  ty: tti::TypeId,
  name: &str,
  seen: &mut HashSet<tti::TypeId>,
) -> Option<tti::TypeId> {
  if !store.contains_type_id(ty) {
    return None;
  }
  let ty = store.canon(ty);
  if !seen.insert(ty) {
    return None;
  }
  match store.type_kind(ty) {
    tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
      let mut collected = Vec::new();
      for member in members.iter().copied() {
        if let Some(prop) = lookup_interned_property_type_inner(store, expander, member, name, seen)
        {
          collected.push(prop);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected))
      }
    }
    tti::TypeKind::Ref { def, args } => {
      let Some(expander) = expander else {
        return None;
      };
      let Some(expanded) = expander.expand_ref(store, def, &args) else {
        return None;
      };
      let expanded = store.canon(expanded);
      // Cycle / no-progress: expand_ref returned the same ref (or another seen id).
      if expanded == ty || seen.contains(&expanded) {
        return None;
      }
      lookup_interned_property_type_inner(store, Some(expander), expanded, name, seen)
    }
    tti::TypeKind::Object(obj_id) => {
      let shape = store.shape(store.object(obj_id).shape);
      for prop in shape.properties.iter() {
        let matches = match prop.key {
          PropKey::String(name_id) => store.name(name_id) == name,
          PropKey::Number(num) => num.to_string() == name,
          _ => false,
        };
        if matches {
          return Some(prop.data.ty);
        }
      }
      let probe_key = if name.parse::<f64>().is_ok() {
        PropKey::Number(0)
      } else {
        PropKey::String(store.intern_name(String::new()))
      };
      for indexer in shape.indexers.iter() {
        if crate::type_queries::indexer_accepts_key(&probe_key, indexer.key_type, store) {
          return Some(indexer.value_type);
        }
      }
      None
    }
    tti::TypeKind::Array { ty, .. } => {
      if name == "length" {
        Some(store.primitive_ids().number)
      } else if name.parse::<i64>().is_ok() {
        // Numeric index → element type. Named methods (`push`, …) are resolved
        // via the lib `Array<T>` interface in the body checker (`member_type`);
        // returning the element type here made `never[].push` look like `never`.
        Some(ty)
      } else {
        None
      }
    }
    _ => None,
  }
}
