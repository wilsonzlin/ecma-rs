use super::super::{
  BodyCheckResult, Diagnostic, FileId, HirExpr, HirExprKind, ProgramState, Span, TypeId, TypeKind,
  CODE_EXCESS_PROPERTY,
};

pub(super) fn is_fresh_object_literal(expr: &HirExpr) -> bool {
  matches!(expr.kind, HirExprKind::Object(_))
}

pub(super) fn check_excess_properties(
  state: &mut ProgramState,
  expr: &HirExpr,
  target_type: TypeId,
  result: &mut BodyCheckResult,
  file: FileId,
) {
  let HirExprKind::Object(props) = &expr.kind else {
    return;
  };

  // Collect candidate target object types. If the target is a union of objects,
  // treat it as a widening of allowed keys; otherwise, only the single object
  // type is considered.
  let mut target_objects = Vec::new();
  match state.type_store.kind(target_type).clone() {
    TypeKind::Object(obj) => target_objects.push(obj),
    TypeKind::Union(types) => {
      for ty in types {
        if let TypeKind::Object(obj) = state.type_store.kind(ty).clone() {
          target_objects.push(obj);
        }
      }
    }
    _ => return,
  };
  if target_objects.is_empty() {
    return;
  }

  // Spread properties are currently ignored for excess checking.
  let literal_props: Vec<_> = props.iter().filter(|p| !p.is_spread).collect();
  if literal_props.is_empty() {
    return;
  }

  let supports_all = target_objects.iter().any(|obj| {
    let allow_index = obj.string_index.is_some() || obj.number_index.is_some();
    literal_props
      .iter()
      .all(|prop| allow_index || obj.props.contains_key(&prop.name))
  });

  if !supports_all {
    let first = literal_props[0];
    result.diagnostics.push(Diagnostic::error(
      CODE_EXCESS_PROPERTY,
      format!("excess property '{}' in object literal", first.name),
      Span {
        file,
        range: first.span,
      },
    ));
    return;
  }

  // Choose a representative target object that covers all literal properties
  // for contextual recursion.
  let target_obj = target_objects.into_iter().find(|obj| {
    let allow_index = obj.string_index.is_some() || obj.number_index.is_some();
    literal_props
      .iter()
      .all(|prop| allow_index || obj.props.contains_key(&prop.name))
  });

  let Some(target_obj) = target_obj else {
    return;
  };

  for prop in literal_props {
    if let HirExprKind::Object(_) = prop.value.kind {
      if let Some(target_prop) = target_obj.props.get(&prop.name).map(|p| p.typ) {
        check_excess_properties(state, &prop.value, target_prop, result, file);
      }
    }
  }
}
