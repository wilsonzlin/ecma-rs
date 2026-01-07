use super::*;

pub(in super::super) fn lookup_interned_property_type(
  store: &tti::TypeStore,
  expander: Option<&dyn tti::RelateTypeExpander>,
  ty: tti::TypeId,
  name: &str,
) -> Option<tti::TypeId> {
  if !store.contains_type_id(ty) {
    return None;
  }
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
      let mut collected = Vec::new();
      for member in members.iter().copied() {
        if let Some(prop) = lookup_interned_property_type(store, expander, member, name) {
          collected.push(prop);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected))
      }
    }
    tti::TypeKind::Ref { def, args } => expander
      .and_then(|exp| exp.expand_ref(store, def, &args))
      .and_then(|expanded| lookup_interned_property_type(store, expander, expanded, name)),
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
      } else {
        Some(ty)
      }
    }
    _ => None,
  }
}
