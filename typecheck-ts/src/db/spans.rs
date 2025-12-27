use std::collections::BTreeMap;
use std::sync::Arc;

use diagnostics::TextRange;
use hir_js::span_map::SpanResult;
use hir_js::{BodyId, ExprId, LowerResult, SpanMap};

/// Per-file span index built from HIR spans.
///
/// This wraps the lowered [`SpanMap`] for a file and augments it with per-body
/// expression spans so lookups can reuse the same tie-breaking logic as
/// [`crate::BodyCheckResult::expr_at`], including special handling for empty
/// spans.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct FileSpanIndex {
  span_map: SpanMap,
  hir_expr_spans: BTreeMap<BodyId, Arc<[TextRange]>>,
}

impl Eq for FileSpanIndex {}

impl FileSpanIndex {
  /// Construct an index from a lowered HIR file.
  pub fn from_lowered(lowered: &LowerResult) -> Self {
    let mut body_ids: Vec<_> = lowered.body_index.keys().copied().collect();
    body_ids.sort_by_key(|id| id.0);

    let mut expr_spans = BTreeMap::new();
    for body_id in body_ids {
      if let Some(body) = lowered.body(body_id) {
        let spans: Vec<_> = body.exprs.iter().map(|expr| expr.span).collect();
        expr_spans.insert(body_id, Arc::from(spans));
      }
    }

    Self {
      span_map: lowered.hir.span_map.clone(),
      hir_expr_spans: expr_spans,
    }
  }

  /// Innermost body covering the offset, based on the lowered span map.
  pub fn body_at(&self, offset: u32) -> Option<BodyId> {
    self
      .span_map
      .expr_span_at_offset(offset)
      .map(|res| res.id.0)
  }

  /// Innermost expression covering the offset, including the span used to select
  /// it (useful for empty-span tie-breaking).
  pub fn expr_at(&self, offset: u32) -> Option<SpanResult<(BodyId, ExprId)>> {
    let body = self.body_at(offset)?;
    let (expr, span) = self.expr_at_in_body(body, offset)?;
    Some(SpanResult {
      range: span,
      id: (body, expr),
    })
  }

  /// Innermost expression covering an offset within a specific body using HIR
  /// spans.
  pub fn expr_at_in_body(&self, body: BodyId, offset: u32) -> Option<(ExprId, TextRange)> {
    let spans = self.hir_expr_spans.get(&body)?;
    expr_at_from_spans(spans, offset)
  }

  /// HIR expression spans recorded for the given body, if present.
  pub fn hir_expr_spans(&self, body: BodyId) -> Option<&[TextRange]> {
    self.hir_expr_spans.get(&body).map(AsRef::as_ref)
  }

  /// Span for a specific expression, if present in the index.
  pub fn span_of_expr(&self, body: BodyId, expr: ExprId) -> Option<TextRange> {
    self
      .hir_expr_spans
      .get(&body)
      .and_then(|spans| spans.get(expr.0 as usize).copied())
  }
}

/// Shared helper to locate the innermost expression covering an offset given a
/// list of spans in evaluation order. This mirrors the behaviour of
/// [`crate::BodyCheckResult::expr_at`] so both program-level queries and
/// per-body results agree on empty-span tie-breaking.
pub fn expr_at_from_spans(spans: &[TextRange], offset: u32) -> Option<(ExprId, TextRange)> {
  let mut best_containing: Option<(ExprId, TextRange)> = None;
  let mut best_empty: Option<(ExprId, TextRange)> = None;

  for (idx, span) in spans.iter().copied().enumerate() {
    if span.start <= offset && offset < span.end {
      match best_containing {
        Some((_, existing)) if existing.len() <= span.len() => {}
        _ => best_containing = Some((ExprId(idx as u32), span)),
      }
    } else if span.is_empty() && offset == span.start {
      match best_empty {
        Some((_, existing)) if existing.len() <= span.len() => {}
        _ => best_empty = Some((ExprId(idx as u32), span)),
      }
    }
  }

  match (best_containing, best_empty) {
    (Some((cont_id, cont_span)), Some((empty_id, empty_span))) => {
      if empty_span.start > cont_span.start && empty_span.end < cont_span.end {
        Some((empty_id, empty_span))
      } else {
        Some((cont_id, cont_span))
      }
    }
    (Some(containing), None) => Some(containing),
    (None, Some(empty)) => Some(empty),
    (None, None) => None,
  }
}
