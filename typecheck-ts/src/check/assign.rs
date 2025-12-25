use super::super::{
  BodyCheckResult, Diagnostic, FileId, HirExpr, ProgramState, Span, TypeId, CODE_TYPE_MISMATCH,
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
  let ctx = state.relate_ctx();
  ctx.is_assignable(source_ty, target_ty)
}
