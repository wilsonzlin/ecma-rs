use super::super::{
  BodyCheckResult, Diagnostic, FileId, HirExpr, ProgramState, Span, TypeId, TypeKind,
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
    let diag_len = result.diagnostics.len();
    object_literal::check_excess_properties(state, expr, source_ty, target_ty, result, file);
    if result.diagnostics.len() > diag_len {
      return false;
    }
    if object_literal::is_fresh_object_literal(expr) {
      if matches!(state.type_store.kind(target_ty), TypeKind::Object(_) | TypeKind::Union(_)) {
        return true;
      }
    } else if matches!(state.type_store.kind(target_ty), TypeKind::Object(_) | TypeKind::Union(_)) {
      // Non-fresh sources skip excess property checks; treat as assignable to
      // object/union targets even if we can't prove structural compatibility.
      return true;
    }
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
  state.is_assignable(source_ty, target_ty)
}
