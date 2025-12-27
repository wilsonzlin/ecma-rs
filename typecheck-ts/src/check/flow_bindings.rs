use hir_js::{
  ids::{ExprId, PatId},
  Body, ExprKind, PatKind,
};
use ::semantic_js::ts::{locals::TsLocalSemantics, SymbolId};

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
        if matches!(expr.kind, ExprKind::Ident(_)) {
          let id = ExprId(idx as u32);
          sem
            .resolve_expr(body, id)
            .or_else(|| sem.resolve_expr_span(expr.span))
        } else {
          None
        }
      })
      .collect();

    let pat = body
      .pats
      .iter()
      .map(|pat| {
        if matches!(pat.kind, PatKind::Ident(_)) {
          sem.resolve_expr_span(pat.span)
        } else {
          None
        }
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
