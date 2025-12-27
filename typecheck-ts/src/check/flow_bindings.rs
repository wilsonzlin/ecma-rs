use hir_js::{
  ids::{ExprId, PatId},
  Body, ExprKind, PatKind,
};
use semantic_js::ts::{locals::TsLocalSemantics, SymbolId};

/// Stable identifier for flow bindings. This reuses the value-namespace symbol
/// identifiers produced by the TS locals binder.
pub type FlowBindingId = SymbolId;

/// Per-body side table mapping identifiers in expressions and patterns back to
/// their resolved bindings.
#[derive(Debug, Clone)]
pub struct FlowBindings {
  expr: Vec<Option<FlowBindingId>>,
  pat: Vec<Option<FlowBindingId>>,
}

impl FlowBindings {
  /// Precompute bindings for all identifier expressions and patterns in a body
  /// so lookups during flow analysis are O(1).
  pub fn new(body: &Body, sem: &TsLocalSemantics) -> Self {
    let expr = body
      .exprs
      .iter()
      .enumerate()
      .map(|(idx, expr)| {
        matches!(expr.kind, ExprKind::Ident(_))
          .then(|| ExprId(idx as u32))
          .and_then(|id| {
            let span = expr.span;
            sem
              .resolve_expr(body, id)
              .or_else(|| sem.resolve_expr_span(span))
              .or_else(|| sem.resolve_expr_at_offset(span.start).map(|(_, id)| id))
              .or_else(|| {
                if span.end > span.start {
                  sem.resolve_expr_at_offset(span.end - 1).map(|(_, id)| id)
                } else {
                  None
                }
              })
          })
      })
      .collect();

    let pat = body
      .pats
      .iter()
      .map(|pat| {
        matches!(pat.kind, PatKind::Ident(_))
          .then(|| pat.span)
          .and_then(|span| {
            sem
              .resolve_expr_span(span)
              .or_else(|| sem.resolve_expr_at_offset(span.start).map(|(_, id)| id))
              .or_else(|| {
                if span.end > span.start {
                  sem.resolve_expr_at_offset(span.end - 1).map(|(_, id)| id)
                } else {
                  None
                }
              })
          })
      })
      .collect();

    Self { expr, pat }
  }

  /// Binding identifier for an expression, if it was an identifier expression
  /// and could be resolved.
  pub fn binding_for_expr(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    self.expr.get(expr_id.0 as usize).copied().flatten()
  }

  /// Binding identifier for a pattern, if it was an identifier pattern and
  /// could be resolved.
  pub fn binding_for_pat(&self, pat_id: PatId) -> Option<FlowBindingId> {
    self.pat.get(pat_id.0 as usize).copied().flatten()
  }
}
