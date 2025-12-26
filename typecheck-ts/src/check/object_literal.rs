use std::cmp::Ordering;

use super::super::{
  BodyCheckResult, FileId, HirExpr, HirExprKind, HirObjectProperty, ObjectType, ProgramState, Span,
  TypeId, TypeKind,
};
use crate::codes;

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
  target_type: TypeId,
  result: &mut BodyCheckResult,
  file: FileId,
) {
  if !is_fresh_object_literal(expr) {
    return;
  }
  let HirExprKind::Object(props) = &expr.kind else {
    return;
  };

  if props.is_empty() || target_type == state.builtin.any || target_type == state.builtin.unknown {
    return;
  }

  let Some(excess) = find_excess_properties(state, target_type, props) else {
    return;
  };

  let note = if excess.allowed.is_empty() {
    None
  } else {
    Some(format!("allowed properties: {}", excess.allowed.join(", ")))
  };

  for prop in excess.extras {
    let name = &prop.name;
    let value = &prop.value;
    let mut diagnostic = codes::EXCESS_PROPERTY.error(
      format!("excess property '{}' in object literal", name),
      Span {
        file,
        range: value.span,
      },
    );
    if let Some(note) = &note {
      diagnostic.push_note(note.clone());
    }
    result.diagnostics.push(diagnostic);
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

struct ExcessResult<'a> {
  extras: Vec<&'a HirObjectProperty>,
  allowed: Vec<String>,
}

fn find_excess_properties<'a>(
  state: &mut ProgramState,
  target_type: TypeId,
  props: &'a [HirObjectProperty],
) -> Option<ExcessResult<'a>> {
  match state.type_store.kind(target_type).clone() {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(obj) => excess_against_object(&obj, props),
    TypeKind::Union(members) => {
      let mut best: Option<ExcessResult> = None;
      for member in members {
        match find_excess_properties(state, member, props) {
          None => return None,
          Some(res) => {
            let replace = match &best {
              None => true,
              Some(current) => {
                res.extras.len() < current.extras.len()
                  || (res.extras.len() == current.extras.len()
                    && res.allowed.cmp(&current.allowed) == Ordering::Less)
              }
            };
            if replace {
              best = Some(res);
            }
          }
        }
      }
      best
    }
    _ => None,
  }
}

fn excess_against_object<'a>(
  target: &ObjectType,
  props: &'a [HirObjectProperty],
) -> Option<ExcessResult<'a>> {
  if target.has_index_signature() || target.props.is_empty() {
    return None;
  }
  let mut extras = Vec::new();
  for prop in props.iter() {
    let name = &prop.name;
    if prop.is_spread {
      continue;
    }
    if !property_allowed(target, name) {
      extras.push(prop);
    }
  }
  if extras.is_empty() {
    None
  } else {
    let mut allowed = allowed_keys(target);
    allowed.sort();
    allowed.dedup();
    Some(ExcessResult { extras, allowed })
  }
}

fn property_allowed(target: &ObjectType, name: &str) -> bool {
  if target.props.contains_key(name) {
    return true;
  }
  if name.parse::<usize>().is_ok() {
    target.number_index.is_some() || target.string_index.is_some()
  } else {
    target.string_index.is_some()
  }
}

fn allowed_keys(target: &ObjectType) -> Vec<String> {
  target.props.keys().cloned().collect()
}
