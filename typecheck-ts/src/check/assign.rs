use super::super::{
  BodyCheckResult, Diagnostic, FileId, HirExpr, ObjectType, ProgramState, Span, TypeId, TypeKind,
  CODE_TYPE_MISMATCH,
};
use super::object_literal;

pub(crate) fn check_assignment(
  state: &mut ProgramState,
  source_expr: Option<&HirExpr>,
  source_ty: TypeId,
  target_ty: TypeId,
  result: &mut BodyCheckResult,
  file: FileId,
) -> bool {
  if target_ty == state.builtin.any || target_ty == state.builtin.unknown {
    return true;
  }

  if let Some(expr) = source_expr {
    object_literal::check_excess_properties(state, expr, source_ty, target_ty, result, file);
  }

  if is_assignable(state, source_ty, target_ty) {
    return true;
  }

  if let Some(expr) = source_expr {
    result.diagnostics.push(Diagnostic::error(
      CODE_TYPE_MISMATCH,
      "type mismatch",
      Span {
        file,
        range: expr.span,
      },
    ));
  }

  false
}

fn is_assignable(state: &mut ProgramState, source_ty: TypeId, target_ty: TypeId) -> bool {
  if target_ty == state.builtin.any || target_ty == state.builtin.unknown {
    return true;
  }

  let source_kind = state.type_store.kind(source_ty).clone();
  match source_kind {
    TypeKind::Any | TypeKind::Unknown => return true,
    _ => {}
  }

  if matches!(state.type_store.kind(target_ty), TypeKind::Void)
    && matches!(source_kind, TypeKind::Undefined)
  {
    return true;
  }

  if source_ty == target_ty {
    return true;
  }

  match state.type_store.kind(target_ty).clone() {
    TypeKind::Union(types) => types
      .into_iter()
      .any(|member| is_assignable(state, source_ty, member)),
    TypeKind::Object(target_obj) => match source_kind {
      TypeKind::Object(source_obj) => is_assignable_object(state, &source_obj, &target_obj),
      _ => false,
    },
    _ => false,
  }
}

fn is_assignable_object(
  state: &mut ProgramState,
  source: &ObjectType,
  target: &ObjectType,
) -> bool {
  for (name, target_prop) in target.props.iter() {
    match source.props.get(name) {
      Some(source_prop) => {
        if !is_assignable(state, source_prop.typ, target_prop.typ) {
          return false;
        }
      }
      None => {
        if !target_prop.optional {
          return false;
        }
      }
    }
  }

  true
}
