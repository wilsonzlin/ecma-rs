use crate::ids::BodyId;
use crate::ids::DefId;
use crate::ids::ExportSpecifierId;
use crate::ids::ExprId;
use crate::ids::ImportSpecifierId;
use crate::ids::PatId;
use crate::ids::TypeExprId;
use diagnostics::TextRange;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

/// An index of expression, definition, and type expression spans that supports
/// deterministic, logarithmic lookups for the innermost span that contains an
/// offset.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct SpanMap {
  exprs: SpanIndex<(BodyId, ExprId)>,
  defs: SpanIndex<DefId>,
  type_exprs: SpanIndex<TypeExprId>,
  pats: SpanIndex<(BodyId, PatId)>,
  import_specifiers: SpanIndex<ImportSpecifierId>,
  export_specifiers: SpanIndex<ExportSpecifierId>,
}

impl SpanMap {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add_expr(&mut self, range: TextRange, body: BodyId, id: ExprId) {
    self.exprs.add(range, (body, id));
  }

  pub fn add_def(&mut self, range: TextRange, id: DefId) {
    self.defs.add(range, id);
  }

  pub fn add_type_expr(&mut self, range: TextRange, id: TypeExprId) {
    self.type_exprs.add(range, id);
  }

  pub fn add_pat(&mut self, range: TextRange, body: BodyId, id: PatId) {
    self.pats.add(range, (body, id));
  }

  pub fn add_import_specifier(&mut self, range: TextRange, id: ImportSpecifierId) {
    self.import_specifiers.add(range, id);
  }

  pub fn add_export_specifier(&mut self, range: TextRange, id: ExportSpecifierId) {
    self.export_specifiers.add(range, id);
  }

  /// Sorts all spans and builds interval indexes for deterministic lookup.
  pub fn finalize(&mut self) {
    self.exprs.finalize();
    self.defs.finalize();
    self.type_exprs.finalize();
    self.pats.finalize();
    self.import_specifiers.finalize();
    self.export_specifiers.finalize();
  }

  /// Returns the innermost expression that contains the offset, preferring the
  /// smallest range length and breaking ties by start offset then id.
  pub fn expr_at_offset(&self, offset: u32) -> Option<(BodyId, ExprId)> {
    self.exprs.query(offset)
  }

  pub fn expr_span_at_offset(&self, offset: u32) -> Option<((BodyId, ExprId), TextRange)> {
    self
      .exprs
      .query_span(offset)
      .map(|span| (span.id, span.range))
  }

  pub fn type_expr_at_offset(&self, offset: u32) -> Option<TypeExprId> {
    self.type_exprs.query(offset)
  }

  pub fn type_expr_span_at_offset(&self, offset: u32) -> Option<(TypeExprId, TextRange)> {
    self
      .type_exprs
      .query_span(offset)
      .map(|span| (span.id, span.range))
  }

  pub fn pat_at_offset(&self, offset: u32) -> Option<(BodyId, PatId)> {
    self.pats.query(offset)
  }

  pub fn pat_span_at_offset(&self, offset: u32) -> Option<((BodyId, PatId), TextRange)> {
    self
      .pats
      .query_span(offset)
      .map(|span| (span.id, span.range))
  }

  pub fn import_specifier_at_offset(&self, offset: u32) -> Option<ImportSpecifierId> {
    self.import_specifiers.query(offset)
  }

  pub fn import_specifier_span_at_offset(
    &self,
    offset: u32,
  ) -> Option<(ImportSpecifierId, TextRange)> {
    self
      .import_specifiers
      .query_span(offset)
      .map(|span| (span.id, span.range))
  }

  pub fn export_specifier_at_offset(&self, offset: u32) -> Option<ExportSpecifierId> {
    self.export_specifiers.query(offset)
  }

  pub fn export_specifier_span_at_offset(
    &self,
    offset: u32,
  ) -> Option<(ExportSpecifierId, TextRange)> {
    self
      .export_specifiers
      .query_span(offset)
      .map(|span| (span.id, span.range))
  }

  /// Returns the innermost definition that contains the offset, preferring the
  /// smallest range length and breaking ties by start offset then id.
  pub fn def_at_offset(&self, offset: u32) -> Option<DefId> {
    self.defs.query(offset)
  }

  pub fn def_span_at_offset(&self, offset: u32) -> Option<(DefId, TextRange)> {
    self
      .defs
      .query_span(offset)
      .map(|span| (span.id, span.range))
  }

  pub fn expr_span(&self, body: BodyId, expr: ExprId) -> Option<TextRange> {
    self.exprs.span_of((body, expr))
  }

  pub fn def_span(&self, def: DefId) -> Option<TextRange> {
    self.defs.span_of(def)
  }

  pub fn type_expr_span(&self, type_expr: TypeExprId) -> Option<TextRange> {
    self.type_exprs.span_of(type_expr)
  }

  pub fn pat_span(&self, body: BodyId, pat: PatId) -> Option<TextRange> {
    self.pats.span_of((body, pat))
  }

  pub fn import_specifier_span(&self, id: ImportSpecifierId) -> Option<TextRange> {
    self.import_specifiers.span_of(id)
  }

  pub fn export_specifier_span(&self, id: ExportSpecifierId) -> Option<TextRange> {
    self.export_specifiers.span_of(id)
  }
}

/// Deterministic interval index for a set of spans keyed by `T`.
#[derive(Debug, Clone, PartialEq)]
pub struct SpanIndex<T> {
  spans: Vec<SpanEntry<T>>,
  segments: Vec<Segment<T>>,
  empties: Vec<ActiveSpan<T>>,
  by_id: BTreeMap<T, ActiveSpan<T>>,
}

impl<T> SpanIndex<T> {
  pub fn new() -> Self {
    Self {
      spans: Vec::new(),
      segments: Vec::new(),
      empties: Vec::new(),
      by_id: BTreeMap::new(),
    }
  }

  pub fn add(&mut self, range: TextRange, id: T)
  where
    T: Copy + Ord,
  {
    let span = ActiveSpan { range, id };
    self.record_by_id(span);
    if range.is_empty() {
      self.empties.push(span);
    } else {
      self.spans.push(SpanEntry { range, id });
    }
  }

  fn record_by_id(&mut self, span: ActiveSpan<T>)
  where
    T: Copy + Ord,
  {
    self
      .by_id
      .entry(span.id)
      .and_modify(|best| {
        if span < *best {
          *best = span;
        }
      })
      .or_insert(span);
  }
}

impl<T: Copy + Ord> SpanIndex<T> {
  /// Build an index from a set of spans in a single pass.
  pub fn from_spans(spans: impl IntoIterator<Item = (TextRange, T)>) -> Self {
    let mut index = SpanIndex::new();
    for (range, id) in spans {
      index.add(range, id);
    }
    index.finalize();
    index
  }

  pub fn finalize(&mut self) {
    self
      .spans
      .sort_by(|a, b| (a.range.start, a.range.end, a.id).cmp(&(b.range.start, b.range.end, b.id)));
    self.segments = build_segments(&self.spans);
    self.empties.sort();
  }

  pub fn query(&self, offset: u32) -> Option<T> {
    self.query_span(offset).map(|span| span.id)
  }

  pub fn query_span(&self, offset: u32) -> Option<SpanResult<T>> {
    let idx = self.segments.partition_point(|seg| seg.end <= offset);
    let best_non_empty = self
      .segments
      .get(idx)
      .and_then(|seg| (offset >= seg.start).then_some(seg.best));

    let start_idx = self
      .empties
      .partition_point(|span| span.range.start < offset);
    let mut best_empty: Option<ActiveSpan<T>> = None;
    for span in self.empties.iter().skip(start_idx) {
      if span.range.start != offset {
        break;
      }
      let replace = best_empty.map(|best| span < &best).unwrap_or(true);
      if replace {
        best_empty = Some(*span);
      }
    }
    match (best_non_empty, best_empty) {
      (None, None) => None,
      (Some(best), None) => Some(best.into()),
      (None, Some(empty)) => Some(empty.into()),
      (Some(best), Some(empty)) => Some(std::cmp::min(best, empty).into()),
    }
  }

  pub fn span_of(&self, id: T) -> Option<TextRange> {
    self.by_id.get(&id).map(|span| span.range)
  }
}

impl<T> Default for SpanIndex<T> {
  fn default() -> Self {
    Self::new()
  }
}

/// Span and identifier returned from span map queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SpanResult<T> {
  pub range: TextRange,
  pub id: T,
}

#[derive(Debug, Clone, PartialEq)]
struct SpanEntry<T> {
  range: TextRange,
  id: T,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ActiveSpan<T> {
  range: TextRange,
  id: T,
}

impl<T> From<ActiveSpan<T>> for SpanResult<T> {
  fn from(value: ActiveSpan<T>) -> Self {
    SpanResult {
      range: value.range,
      id: value.id,
    }
  }
}

impl<T: Copy> ActiveSpan<T> {
  fn len(&self) -> u32 {
    self.range.len()
  }
}

impl<T: Ord + Copy> Ord for ActiveSpan<T> {
  fn cmp(&self, other: &Self) -> Ordering {
    (self.len(), self.range.start, self.id, self.range.end).cmp(&(
      other.len(),
      other.range.start,
      other.id,
      other.range.end,
    ))
  }
}

impl<T: Ord + Copy> PartialOrd for ActiveSpan<T> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

#[derive(Debug, Clone, PartialEq)]
struct Segment<T> {
  start: u32,
  end: u32,
  best: ActiveSpan<T>,
}

impl<T> Segment<T> {
  fn new(start: u32, end: u32, best: ActiveSpan<T>) -> Self {
    Self { start, end, best }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EventKind {
  End,
  Start,
}

#[derive(Clone, Copy)]
struct Event<T> {
  pos: u32,
  kind: EventKind,
  span: ActiveSpan<T>,
}

fn build_segments<T: Copy + Ord>(spans: &[SpanEntry<T>]) -> Vec<Segment<T>> {
  let mut events = Vec::with_capacity(spans.len() * 2);
  for entry in spans {
    if entry.range.is_empty() {
      continue;
    }

    let span = ActiveSpan {
      range: entry.range,
      id: entry.id,
    };

    events.push(Event {
      pos: entry.range.start,
      kind: EventKind::Start,
      span,
    });
    events.push(Event {
      pos: entry.range.end,
      kind: EventKind::End,
      span,
    });
  }

  events.sort_by(|a, b| {
    a.pos
      .cmp(&b.pos)
      .then_with(|| a.kind.cmp(&b.kind))
      .then_with(|| a.span.cmp(&b.span))
  });

  let mut active: BTreeSet<ActiveSpan<T>> = BTreeSet::new();
  let mut segments = Vec::new();
  let mut idx = 0usize;
  let mut prev_pos: Option<u32> = None;
  let mut best: Option<ActiveSpan<T>> = None;

  while idx < events.len() {
    let pos = events[idx].pos;
    if let Some(prev) = prev_pos {
      if prev < pos {
        if let Some(best_span) = best {
          push_segment(&mut segments, prev, pos, best_span);
        }
      }
    }

    let mut end_idx = idx;
    while end_idx < events.len() && events[end_idx].pos == pos {
      end_idx += 1;
    }

    for event in &events[idx..end_idx] {
      if matches!(event.kind, EventKind::End) {
        active.remove(&event.span);
      }
    }
    for event in &events[idx..end_idx] {
      if matches!(event.kind, EventKind::Start) {
        active.insert(event.span);
      }
    }

    best = active.iter().next().copied();
    prev_pos = Some(pos);
    idx = end_idx;
  }

  segments
}

fn push_segment<T: Copy + Ord>(
  segments: &mut Vec<Segment<T>>,
  start: u32,
  end: u32,
  best: ActiveSpan<T>,
) {
  if let Some(prev) = segments.last_mut() {
    if prev.best == best && prev.end == start {
      prev.end = end;
      return;
    }
  }
  segments.push(Segment::new(start, end, best));
}

#[cfg(test)]
mod tests {
  use super::SpanMap;
  use crate::ids::BodyId;
  use crate::ids::DefId;
  use crate::ids::ExportSpecifierId;
  use crate::ids::ExprId;
  use crate::ids::ImportSpecifierId;
  use crate::ids::PatId;
  use crate::ids::TypeExprId;
  use diagnostics::TextRange;
  use std::time::Instant;

  use super::SpanIndex;

  #[test]
  fn selects_innermost_span_for_offset() {
    let index = SpanIndex::from_spans([
      (TextRange::new(0, 10), 0u32),
      (TextRange::new(2, 8), 1u32),
      (TextRange::new(4, 6), 2u32),
    ]);

    let result = index.query_span(5).expect("span at offset");
    assert_eq!(result.id, 2);
    assert_eq!(result.range, TextRange::new(4, 6));
  }

  #[test]
  fn prefers_inner_expr() {
    let mut map = SpanMap::new();
    map.add_expr(TextRange::new(0, 10), BodyId(0), ExprId(0));
    map.add_expr(TextRange::new(2, 4), BodyId(0), ExprId(1));
    map.finalize();
    assert_eq!(map.expr_at_offset(3), Some((BodyId(0), ExprId(1))));
  }

  #[test]
  fn prefers_empty_span_at_offset() {
    let mut map = SpanMap::new();
    map.add_expr(TextRange::new(0, 10), BodyId(0), ExprId(0));
    map.add_expr(TextRange::new(5, 5), BodyId(0), ExprId(1));
    map.finalize();

    assert_eq!(map.expr_at_offset(5), Some((BodyId(0), ExprId(1))));
    let ((body, id), span) = map.expr_span_at_offset(5).expect("span for empty expr");
    assert_eq!(body, BodyId(0));
    assert_eq!(id, ExprId(1));
    assert_eq!(span, TextRange::new(5, 5));
  }

  #[test]
  fn def_lookup_is_stable() {
    let mut map = SpanMap::new();
    map.add_def(TextRange::new(0, 5), DefId(0));
    map.add_def(TextRange::new(0, 4), DefId(1));
    map.finalize();
    assert_eq!(map.def_at_offset(1), Some(DefId(1)));
  }

  #[test]
  fn span_lookup_prefers_inner_range_for_id() {
    let mut index = SpanIndex::new();
    index.add(TextRange::new(0, 10), ExprId(0));
    index.add(TextRange::new(2, 5), ExprId(0));
    index.finalize();

    assert_eq!(index.span_of(ExprId(0)), Some(TextRange::new(2, 5)));
  }

  #[test]
  fn handles_many_spans_quickly() {
    let mut map = SpanMap::new();
    // Generate nested spans so every offset is covered by many ranges and the
    // innermost result changes frequently.
    let span_count: u32 = 10_000;
    for i in 0..span_count {
      let start = i;
      let end = i + span_count + 1;
      map.add_expr(TextRange::new(start, end), BodyId(0), ExprId(i));
    }
    map.finalize();

    let start = Instant::now();
    let mut last = None;
    // Query enough offsets to catch regressions without depending on external
    // benchmarking infrastructure.
    for offset in 0..span_count {
      let mapped = map.expr_at_offset(offset).expect("expr at offset");
      last = Some(mapped);
    }
    // A simple sanity check to keep the optimizer from removing the loop.
    assert!(last.is_some());
    // Ensure the lookup path remains efficient in debug builds.
    assert!(
      start.elapsed().as_secs_f32() < 2.0,
      "span map lookup took too long"
    );
  }

  #[test]
  fn type_expr_lookup_prefers_inner_span() {
    let mut map = SpanMap::new();
    map.add_type_expr(TextRange::new(0, 10), TypeExprId(0));
    map.add_type_expr(TextRange::new(2, 5), TypeExprId(1));
    map.finalize();

    assert_eq!(map.type_expr_at_offset(3), Some(TypeExprId(1)));
  }

  #[test]
  fn pat_and_import_export_lookup_work() {
    let mut map = SpanMap::new();
    map.add_pat(TextRange::new(0, 2), BodyId(0), PatId(1));
    map.add_import_specifier(TextRange::new(4, 6), ImportSpecifierId(2));
    map.add_export_specifier(TextRange::new(8, 10), ExportSpecifierId(3));
    map.finalize();

    assert_eq!(map.pat_at_offset(1), Some((BodyId(0), PatId(1))));
    assert_eq!(
      map.import_specifier_at_offset(5),
      Some(ImportSpecifierId(2))
    );
    assert_eq!(
      map.export_specifier_at_offset(9),
      Some(ExportSpecifierId(3))
    );
  }

  #[test]
  fn expr_lookup_reports_body() {
    let mut map = SpanMap::new();
    map.add_expr(TextRange::new(0, 10), BodyId(0), ExprId(0));
    map.add_expr(TextRange::new(2, 4), BodyId(1), ExprId(0));
    map.finalize();

    let ((body, expr), span) = map.expr_span_at_offset(3).expect("expr with body");
    assert_eq!(body, BodyId(1));
    assert_eq!(expr, ExprId(0));
    assert_eq!(span, TextRange::new(2, 4));
  }

  #[test]
  fn expr_span_lookup_uses_body() {
    let mut map = SpanMap::new();
    map.add_expr(TextRange::new(0, 10), BodyId(0), ExprId(0));
    map.add_expr(TextRange::new(0, 10), BodyId(1), ExprId(0));
    map.finalize();

    assert_eq!(
      map.expr_span(BodyId(1), ExprId(0)),
      Some(TextRange::new(0, 10))
    );
    assert_eq!(
      map.expr_span(BodyId(0), ExprId(0)),
      Some(TextRange::new(0, 10))
    );
  }
}
