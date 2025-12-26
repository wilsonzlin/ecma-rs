use super::super::{BodyCheckResult, FileId, HirExpr, ProgramState, Span, TypeId};
use super::object_literal;
use crate::codes;

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
    object_literal::check_excess_properties(state, expr, target_ty, result, file);
  }

  if state.is_assignable(source_ty, target_ty) {
    return true;
  }

  if let Some(expr) = source_expr {
    result.diagnostics.push(codes::TYPE_MISMATCH.error(
      "type mismatch",
      Span {
        file,
        range: expr.span,
      },
    ));
  }

  false
}
