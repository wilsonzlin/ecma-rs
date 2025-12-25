use super::super::{
  BodyCheckResult, Diagnostic, FileId, HirExpr, HirExprKind, ObjectType, ProgramState, Span,
  TypeId, TypeKind, CODE_EXCESS_PROPERTY,
};

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

  let source_kind = state.type_store.kind(source_type).clone();
  let TypeKind::Object(source_obj) = source_kind else {
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
      let extras: Vec<String> = source_obj
        .props
        .keys()
        .filter(|key| !target_obj.props.contains_key(*key))
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
