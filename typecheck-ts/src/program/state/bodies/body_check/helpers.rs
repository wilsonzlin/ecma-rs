use super::*;

// JSX tag names are not represented as `ExprKind::Ident` in HIR, so we need to
// collect component tag bases explicitly. This lets the body checker include
// value bindings for imported/global components referenced only from JSX (e.g.
// `<Foo />` or `<Foo.Bar />`).
//
// NOTE: JSX tag names containing `:` (namespaced) or `-` (custom elements)
// should always be treated as intrinsic elements and must not be seeded as
// value identifiers, regardless of capitalization.
pub(super) fn collect_jsx_root_names(
  element: &hir_js::JsxElement,
  lowered: &hir_js::LowerResult,
  names: &mut HashSet<String>,
) {
  if let Some(name) = element.name.as_ref() {
    match name {
      hir_js::JsxElementName::Member(member) => {
        if let Some(base) = lowered.names.resolve(member.base) {
          if !(base.contains(':') || base.contains('-')) {
            names.insert(base.to_string());
          }
        }
      }
      hir_js::JsxElementName::Ident(name_id) => {
        if let Some(name) = lowered.names.resolve(*name_id) {
          if !(name.contains(':') || name.contains('-')) {
            if let Some(first_char) = name.chars().next() {
              if !first_char.is_ascii_lowercase() {
                names.insert(name.to_string());
              }
            }
          }
        }
      }
      hir_js::JsxElementName::Name(_) => {}
    }
  }
  // Nested JSX elements are lowered as separate `ExprKind::Jsx` expressions, so
  // they will be visited by the outer `body.exprs` scan that calls this helper.
}

pub(super) fn record_param_pats(
  body: &hir_js::Body,
  pat_id: HirPatId,
  pat_types: &[TypeId],
  unknown: TypeId,
  initial_env: &mut HashMap<NameId, TypeId>,
) {
  let Some(pat) = body.pats.get(pat_id.0 as usize) else {
    return;
  };
  match &pat.kind {
    HirPatKind::Ident(name_id) => {
      if let Some(ty) = pat_types.get(pat_id.0 as usize).copied() {
        if ty != unknown {
          initial_env.insert(*name_id, ty);
        }
      }
    }
    HirPatKind::Array(arr) => {
      for elem in arr.elements.iter().flatten() {
        record_param_pats(body, elem.pat, pat_types, unknown, initial_env);
      }
      if let Some(rest) = arr.rest {
        record_param_pats(body, rest, pat_types, unknown, initial_env);
      }
    }
    HirPatKind::Object(obj) => {
      for prop in obj.props.iter() {
        record_param_pats(body, prop.value, pat_types, unknown, initial_env);
      }
      if let Some(rest) = obj.rest {
        record_param_pats(body, rest, pat_types, unknown, initial_env);
      }
    }
    HirPatKind::Rest(inner) => {
      record_param_pats(body, **inner, pat_types, unknown, initial_env);
    }
    HirPatKind::Assign { target, .. } => {
      record_param_pats(body, *target, pat_types, unknown, initial_env);
    }
    HirPatKind::AssignTarget(_) => {}
  }
}

pub(super) fn prop_type(store: &tti::TypeStore, ty: TypeId, name: &str) -> Option<TypeId> {
  match store.type_kind(ty).clone() {
    tti::TypeKind::Object(obj) => {
      let obj = store.object(obj);
      let shape = store.shape(obj.shape);
      for prop in shape.properties.iter() {
        if let tti::PropKey::String(sym) = prop.key {
          if store.name(sym) == name {
            return Some(prop.data.ty);
          }
        }
      }
      let probe_key = if name.parse::<f64>().is_ok() {
        tti::PropKey::Number(0)
      } else {
        tti::PropKey::String(store.intern_name(String::new()))
      };
      for indexer in shape.indexers.iter() {
        if crate::type_queries::indexer_accepts_key(&probe_key, indexer.key_type, store) {
          return Some(indexer.value_type);
        }
      }
      None
    }
    tti::TypeKind::Union(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(ty) = prop_type(store, member, name) {
          collected.push(ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected))
      }
    }
    _ => None,
  }
}
