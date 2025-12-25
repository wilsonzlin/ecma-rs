use super::super::{
  lookup_property_type, BodyCheckResult, Diagnostic, FileId, HirExpr, HirExprKind, ProgramState,
  Span, TypeId, TypeKind, CODE_EXCESS_PROPERTY,
};
use std::collections::HashSet;

pub(super) fn is_fresh_object_literal(expr: &HirExpr) -> bool {
  matches!(expr.kind, HirExprKind::Object(_))
}

pub(super) fn check_excess_properties(
  state: &mut ProgramState,
  expr: &HirExpr,
  source_type: TypeId,
  target_type: TypeId,
  result: &mut BodyCheckResult,
  file: FileId,
) {
  if !is_fresh_object_literal(expr) {
    return;
  }

  let source_kind = state.type_store.type_kind(source_type);
  let TypeKind::Object(source_obj) = source_kind else {
    return;
  };

  if let Some(excess) = excess_keys(state, target_type, source_obj) {
    for key in excess {
      result.diagnostics.push(Diagnostic::error(
        CODE_EXCESS_PROPERTY,
        format!("excess property '{}' in object literal", key),
        Span {
          file,
          range: expr.span,
        },
      ));
    }
  }

  if let HirExprKind::Object(props) = &expr.kind {
    for (name, value) in props.iter() {
      if name == "..." {
        continue;
      }
      if let HirExprKind::Object(_) = value.kind {
        if let Some(target_prop) = contextual_property_type(state, target_type, name) {
          let source_prop = lookup_property_type(state.type_store.as_ref(), source_type, name)
            .unwrap_or(state.builtin.unknown);
          check_excess_properties(state, value, source_prop, target_prop, result, file);
        }
      }
    }
  }
}

fn contextual_property_type(state: &ProgramState, target: TypeId, name: &str) -> Option<TypeId> {
  match state.type_store.type_kind(target) {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(_) => lookup_property_type(state.type_store.as_ref(), target, name),
    TypeKind::Union(types) => {
      let mut collected = Vec::new();
      for ty in types {
        if let Some(prop_ty) = contextual_property_type(state, ty, name) {
          collected.push(prop_ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(state.type_store.union(collected))
      }
    }
    _ => None,
  }
}

fn excess_keys(
  state: &mut ProgramState,
  target_type: TypeId,
  source_obj: types_ts_interned::ObjectId,
) -> Option<Vec<String>> {
  match state.type_store.type_kind(target_type) {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(target_obj) => {
      let target_shape = state
        .type_store
        .shape(state.type_store.object(target_obj).shape);
      if !target_shape.indexers.is_empty() {
        return None;
      }
      let target_keys: Vec<String> = target_shape
        .properties
        .iter()
        .filter_map(|p| match &p.key {
          types_ts_interned::PropKey::String(id) => Some(state.type_store.name(*id)),
          _ => None,
        })
        .collect();
      let target_set: HashSet<_> = target_keys.into_iter().collect();
      let source_shape = state
        .type_store
        .shape(state.type_store.object(source_obj).shape);
      let extras: Vec<String> = source_shape
        .properties
        .iter()
        .filter_map(|p| match &p.key {
          types_ts_interned::PropKey::String(id) => Some(state.type_store.name(*id)),
          _ => None,
        })
        .filter(|key| !target_set.contains(key))
        .collect();
      if extras.is_empty() {
        None
      } else {
        Some(extras)
      }
    }
    TypeKind::Union(types) => {
      let mut best: Option<Vec<String>> = None;
      for member in types {
        match excess_keys(state, member, source_obj) {
          None => return None,
          Some(keys) => {
            if best.as_ref().map_or(true, |b| keys.len() < b.len()) {
              best = Some(keys);
            }
          }
        }
      }
      best
    }
    _ => None,
  }
}
