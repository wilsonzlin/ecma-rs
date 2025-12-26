use std::collections::HashSet;

use super::super::{
  Diagnostic, FileId, HirExpr, HirExprKind, ObjectType, ProgramState, Span, TypeId, TypeKind,
  CODE_EXCESS_PROPERTY,
};
use super::body::BodyCheckOutput;

pub(crate) fn is_fresh_object_literal(expr: &HirExpr) -> bool {
  matches!(expr.kind, HirExprKind::Object(_))
}

/// Return the contextual type for a property on an object literal when the target type is known.
pub(crate) fn contextual_property_type(
  state: &mut ProgramState,
  target: TypeId,
  name: &str,
) -> Option<TypeId> {
  match state.type_store.kind(target).clone() {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(obj) => property_type_from_object(&obj, name),
    TypeKind::Union(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(ty) = contextual_property_type(state, member, name) {
          collected.push(ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(state.type_store.union(collected, &state.builtin))
      }
    }
    _ => None,
  }
}

pub(crate) fn check_excess_properties(
  state: &mut ProgramState,
  expr: &HirExpr,
  source_type: TypeId,
  target_type: TypeId,
  result: &mut BodyCheckOutput,
  file: FileId,
) {
  if !is_fresh_object_literal(expr) {
    return;
  }
  if !matches!(expr.kind, HirExprKind::Object(_)) {
    return;
  };

  let Some(source_obj) = expect_object_type(state, source_type) else {
    return;
  };

  if let Some(excess) = excess_keys(state, target_type, &source_obj) {
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
}

fn expect_object_type(state: &ProgramState, ty: TypeId) -> Option<ObjectType> {
  match state.type_store.kind(ty) {
    TypeKind::Object(obj) => Some(obj.clone()),
    TypeKind::Union(members) => {
      members
        .iter()
        .find_map(|member| match state.type_store.kind(*member) {
          TypeKind::Object(obj) => Some(obj.clone()),
          _ => None,
        })
    }
    _ => None,
  }
}

fn excess_keys(
  state: &mut ProgramState,
  target_type: TypeId,
  source_obj: &ObjectType,
) -> Option<Vec<String>> {
  match state.type_store.kind(target_type).clone() {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(target_obj) => {
      if target_obj.has_index_signature() {
        return None;
      }
      let target_keys: HashSet<String> = target_obj.props.keys().cloned().collect();
      let extras: Vec<String> = source_obj
        .props
        .keys()
        .filter(|key| !target_keys.contains(*key))
        .cloned()
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

fn property_type_from_object(obj: &ObjectType, name: &str) -> Option<TypeId> {
  if let Some(prop) = obj.props.get(name) {
    return Some(prop.typ);
  }
  if name.parse::<usize>().is_ok() {
    obj.number_index.or(obj.string_index)
  } else {
    obj.string_index
  }
}
