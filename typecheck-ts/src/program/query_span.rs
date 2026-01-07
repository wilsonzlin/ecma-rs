use std::time::Instant;

use crate::profile::{QueryKind, QueryStatsCollector, QueryTimer};
use types_ts_interned::TypeId;

macro_rules! query_span {
  ($name:literal, $file:expr, $def:expr, $body:expr, $cache_hit:expr) => {
    tracing::debug_span!(
      $name,
      file = $file,
      def = $def,
      body = $body,
      type_id = tracing::field::Empty,
      cache_hit = $cache_hit,
      duration_ms = tracing::field::Empty,
    )
  };
}

/// Lightweight helper for emitting structured tracing spans around query-like
/// boundaries. When tracing is disabled, this is a no-op to keep hot paths
/// cheap.
pub(super) struct QuerySpan {
  span: tracing::Span,
  start: Instant,
  span_enabled: bool,
  timer: Option<QueryTimer>,
}

impl QuerySpan {
  pub(super) fn enter(
    kind: QueryKind,
    span: tracing::Span,
    type_id: Option<TypeId>,
    cache_hit: bool,
    query_stats: Option<QueryStatsCollector>,
  ) -> Option<QuerySpan> {
    let span_enabled = !span.is_disabled();
    if !span_enabled && query_stats.is_none() {
      return None;
    }
    let start = Instant::now();
    let timer = query_stats.map(|stats| stats.timer_with_start(kind, cache_hit, start));
    if span_enabled {
      if let Some(ty) = type_id {
        span.record("type_id", ty.0);
      }
      let _guard = span.enter();
      drop(_guard);
    }
    Some(QuerySpan {
      span,
      start,
      span_enabled,
      timer,
    })
  }

  pub(super) fn finish(self, type_id: Option<TypeId>) {
    let duration = self.start.elapsed();
    if let Some(timer) = self.timer {
      timer.finish_with_duration(duration);
    }
    if self.span_enabled {
      if let Some(ty) = type_id {
        self.span.record("type_id", ty.0);
      }
      self
        .span
        .record("duration_ms", duration.as_secs_f64() * 1000.0);
    }
  }
}

