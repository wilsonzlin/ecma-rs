use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{DefId, DefKind as HirDefKind, LowerResult};
use semantic_js::ts::TsProgramSemantics;
use types_ts_interned::{
  self as tti, ObjectType, PropData, PropKey, Property, TypeId, TypeKind, TypeStore,
};

use crate::db::types::DeclTypes;
use crate::program::check::decls::HirDeclLowerer;
use crate::{FileKey, Host};

/// Lower declaration type information for a single file using the provided
/// interning store and optional semantic context.
pub fn lower_decl_types(
  store: Arc<TypeStore>,
  lowered: &LowerResult,
  semantics: Option<&TsProgramSemantics>,
  defs: Arc<HashMap<(FileId, String), DefId>>,
  file: FileId,
  file_key: Option<FileKey>,
  host: Option<&dyn Host>,
  key_to_id: Option<&dyn Fn(&FileKey) -> Option<FileId>>,
  module_namespace_defs: Option<&HashMap<FileId, DefId>>,
  value_defs: Option<&HashMap<DefId, DefId>>,
) -> DeclTypes {
  let mut decls = DeclTypes::default();
  let mut def_map = HashMap::new();
  let mut local_defs = HashMap::new();
  for def in lowered.defs.iter() {
    if let Some(name) = lowered.names.resolve(def.name) {
      let name = name.to_string();
      local_defs.insert(name.clone(), def.id);
      if let Some(mapped) = defs.get(&(file, name.clone())) {
        def_map.insert(def.id, *mapped);
      }
    }
  }

  let mut sorted_defs = lowered.defs.clone();
  sorted_defs.sort_by_key(|def| (def.span.start, def.span.end, def.id.0));

  let defs_owned = defs.as_ref().clone();
  let mut lowerer = HirDeclLowerer::new(
    Arc::clone(&store),
    &lowered.types,
    semantics,
    defs_owned,
    file,
    file_key,
    local_defs,
    &mut decls.diagnostics,
    Some(&def_map),
    Some(defs.as_ref()),
    host,
    key_to_id,
    module_namespace_defs,
    value_defs,
  );
  for def in sorted_defs.iter() {
    let Some(info) = def.type_info.as_ref() else {
      continue;
    };
    let target_def = def_map
      .get(&def.id)
      .copied()
      .or_else(|| {
        lowered
          .names
          .resolve(def.name)
          .and_then(|name| defs.get(&(file, name.to_string())).copied())
      })
      .unwrap_or(def.id);

    if let hir_js::DefTypeInfo::TypeAlias { type_expr, .. } = info {
      if let Some(name) = lowered.names.resolve(def.name) {
        if let Some(kind) = tti::IntrinsicKind::from_name(name) {
          if let Some(arenas) = lowered.type_arenas(def.id) {
            if type_expr_is_intrinsic_marker(arenas, &lowered.names, *type_expr) {
              decls.intrinsics.insert(target_def, kind);
            }
          }
        }
      }
    }

    match info {
      hir_js::DefTypeInfo::Class { .. } => {
        let Some((instance, value, params)) =
          lowerer.lower_class_instance_and_value_types(def.id, info, &lowered.names)
        else {
          continue;
        };
        decls
          .types
          .entry(target_def)
          .and_modify(|existing| {
            *existing = merge_interned_decl_types(&store, *existing, instance);
          })
          .or_insert(instance);
        if !params.is_empty() {
          decls.type_params.insert(target_def, params);
        }
        if let Some(value_defs) = value_defs {
          if let Some(value_def) = value_defs
            .get(&target_def)
            .copied()
            .or_else(|| value_defs.get(&def.id).copied())
          {
            decls
              .types
              .entry(value_def)
              .and_modify(|existing| {
                *existing = merge_interned_decl_types(&store, *existing, value);
              })
              .or_insert(value);
          }
        }
      }
      hir_js::DefTypeInfo::Enum { .. } => {
        let Some((enum_ty, value)) =
          lowerer.lower_enum_type_and_value(def.id, info, &lowered.names)
        else {
          continue;
        };
        decls
          .types
          .entry(target_def)
          .and_modify(|existing| {
            *existing = merge_interned_decl_types(&store, *existing, enum_ty);
          })
          .or_insert(enum_ty);
        if let Some(value_defs) = value_defs {
          if let Some(value_def) = value_defs
            .get(&target_def)
            .copied()
            .or_else(|| value_defs.get(&def.id).copied())
          {
            decls
              .types
              .entry(value_def)
              .and_modify(|existing| {
                *existing = merge_interned_decl_types(&store, *existing, value);
              })
              .or_insert(value);
          }
        }
      }
      _ => {
        let (ty, params) = lowerer.lower_type_info(def.id, info, &lowered.names);
        decls
          .types
          .entry(target_def)
          .and_modify(|existing| {
            *existing = merge_interned_decl_types(&store, *existing, ty);
          })
          .or_insert(ty);
        if !params.is_empty() {
          decls.type_params.insert(target_def, params);
        }
      }
    }
  }

  for ns_def in sorted_defs
    .iter()
    .filter(|d| matches!(d.path.kind, HirDefKind::Namespace | HirDefKind::Module))
  {
    let Some(ns_name) = lowered.names.resolve(ns_def.name) else {
      continue;
    };
    let target_def = def_map.get(&ns_def.id).copied().unwrap_or(ns_def.id);
    let mut members = Vec::new();
    for member in sorted_defs.iter() {
      if member.id == ns_def.id {
        continue;
      }
      if member.span.start >= ns_def.span.start && member.span.end <= ns_def.span.end {
        if let Some(name) = lowered.names.resolve(member.name) {
          members.push(name.to_string());
        }
      }
    }
    members.sort();
    members.dedup();
    if !members.is_empty() {
      decls.namespace_members.insert(target_def, members);
    }
    if !decls.namespace_members.contains_key(&target_def) {
      decls
        .namespace_members
        .insert(target_def, vec![ns_name.to_string()]);
    }
  }

  decls
}

fn type_expr_is_intrinsic_marker(
  arenas: &hir_js::TypeArenas,
  names: &hir_js::NameInterner,
  mut type_expr: hir_js::TypeExprId,
) -> bool {
  loop {
    let Some(expr) = arenas.type_exprs.get(type_expr.0 as usize) else {
      return false;
    };
    match &expr.kind {
      hir_js::TypeExprKind::Parenthesized(inner) => {
        type_expr = *inner;
      }
      hir_js::TypeExprKind::Intrinsic => return true,
      hir_js::TypeExprKind::TypeRef(type_ref) => {
        if !type_ref.type_args.is_empty() {
          return false;
        }
        return matches!(&type_ref.name, hir_js::TypeName::Ident(id) if names.resolve(*id) == Some("intrinsic"));
      }
      _ => return false,
    }
  }
}

pub fn merge_interned_decl_types(
  store: &Arc<TypeStore>,
  existing: TypeId,
  incoming: TypeId,
) -> TypeId {
  match (store.type_kind(existing), store.type_kind(incoming)) {
    (
      TypeKind::Callable {
        overloads: existing_overloads,
      },
      TypeKind::Callable {
        overloads: incoming_overloads,
      },
    ) => {
      let existing_unknown = existing_overloads.iter().all(|sig_id| {
        matches!(
          store.type_kind(store.signature(*sig_id).ret),
          TypeKind::Unknown
        )
      });
      if existing_unknown {
        return store.intern_type(TypeKind::Callable {
          overloads: incoming_overloads,
        });
      }
      let mut merged = existing_overloads.clone();
      merged.extend(incoming_overloads.iter().copied());
      merged.sort_by(|a, b| store.compare_signatures(*a, *b));
      merged.dedup();
      store.intern_type(TypeKind::Callable { overloads: merged })
    }
    (TypeKind::Object(obj_a), TypeKind::Object(obj_b)) => {
      let mut shape = store.shape(store.object(obj_a).shape);
      let other = store.shape(store.object(obj_b).shape);
      let mut merged = Vec::new();
      for prop in shape
        .properties
        .into_iter()
        .chain(other.properties.into_iter())
      {
        if let Some(existing) = merged
          .iter_mut()
          .find(|p: &&mut Property| p.key == prop.key)
        {
          *existing = prop;
        } else {
          merged.push(prop);
        }
      }
      shape.properties = merged;
      shape.call_signatures.extend(other.call_signatures);
      shape
        .construct_signatures
        .extend(other.construct_signatures);
      shape.indexers.extend(other.indexers);
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(ObjectType { shape: shape_id });
      store.intern_type(TypeKind::Object(obj_id))
    }
    _ => store.intersection(vec![existing, incoming]),
  }
}

/// Helper to build a namespace object type with placeholder member types.
pub fn build_namespace_object_type(
  store: &Arc<TypeStore>,
  existing: Option<TypeId>,
  members: &[String],
) -> TypeId {
  let mut shape = existing
    .and_then(|ty| match store.type_kind(ty) {
      TypeKind::Object(obj) => Some(store.shape(store.object(obj).shape)),
      _ => None,
    })
    .unwrap_or_else(tti::Shape::new);
  for name in members.iter() {
    let key = PropKey::String(store.intern_name(name.clone()));
    shape.properties.push(Property {
      key,
      data: PropData {
        ty: store.primitive_ids().any,
        optional: false,
        readonly: true,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}
