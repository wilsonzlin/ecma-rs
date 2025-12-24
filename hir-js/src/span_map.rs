use crate::ids::DefId;
use crate::ids::ExprId;
use diagnostics::TextRange;
use std::cmp::Ordering;
use std::collections::BTreeSet;

/// An index of expression and definition spans that supports deterministic,
/// logarithmic lookups for the innermost span that contains an offset.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct SpanMap {
  exprs: SpanIndex<ExprId>,
  defs: SpanIndex<DefId>,
}

impl SpanMap {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add_expr(&mut self, range: TextRange, id: ExprId) {
    self.exprs.add(range, id);
  }

  pub fn add_def(&mut self, range: TextRange, id: DefId) {
    self.defs.add(range, id);
  }

  /// Sorts all spans and builds interval indexes for deterministic lookup.
  pub fn finalize(&mut self) {
    self.exprs.finalize();
    self.defs.finalize();
  }

  /// Returns the innermost expression that contains the offset, preferring the
  /// smallest range length and breaking ties by start offset then id.
  pub fn expr_at_offset(&self, offset: u32) -> Option<ExprId> {
    self.exprs.query(offset)
  }

  /// Returns the innermost definition that contains the offset, preferring the
  /// smallest range length and breaking ties by start offset then id.
  pub fn def_at_offset(&self, offset: u32) -> Option<DefId> {
    self.defs.query(offset)
  }
}

/// Deterministic interval index for a set of spans keyed by `T`.
#[derive(Debug, Clone, PartialEq)]
struct SpanIndex<T> {
  spans: Vec<SpanEntry<T>>,
  segments: Vec<Segment<T>>,
}

impl<T> SpanIndex<T> {
  fn new() -> Self {
    Self {
      spans: Vec::new(),
      segments: Vec::new(),
    }
  }

  fn add(&mut self, range: TextRange, id: T) {
    self.spans.push(SpanEntry { range, id });
  }
}

impl<T: Copy + Ord> SpanIndex<T> {
  fn finalize(&mut self) {
    self
      .spans
      .sort_by(|a, b| (a.range.start, a.range.end, a.id).cmp(&(b.range.start, b.range.end, b.id)));
    self.segments = build_segments(&self.spans);
  }

  fn query(&self, offset: u32) -> Option<T> {
    let idx = self.segments.partition_point(|seg| seg.end <= offset);
    let seg = self.segments.get(idx)?;
    if offset < seg.start {
      None
    } else {
      Some(seg.best.id)
    }
  }
}

impl<T> Default for SpanIndex<T> {
  fn default() -> Self {
    Self::new()
  }
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
  use crate::ids::DefId;
  use crate::ids::ExprId;
  use diagnostics::TextRange;
  use std::time::Instant;

  #[test]
  fn prefers_inner_expr() {
    let mut map = SpanMap::new();
    map.add_expr(TextRange::new(0, 10), ExprId(0));
    map.add_expr(TextRange::new(2, 4), ExprId(1));
    map.finalize();
    assert_eq!(map.expr_at_offset(3), Some(ExprId(1)));
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
  fn handles_many_spans_quickly() {
    let mut map = SpanMap::new();
    // Generate nested spans so every offset is covered by many ranges and the
    // innermost result changes frequently.
    let span_count: u32 = 10_000;
    for i in 0..span_count {
      let start = i;
      let end = i + span_count + 1;
      map.add_expr(TextRange::new(start, end), ExprId(i));
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
      start.elapsed().as_secs_f32() < 1.0,
      "span map lookup took too long"
    );
  }
}
