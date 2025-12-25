use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// Named query boundaries used for tracing and profiling.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum QueryKind {
  Parse,
  LowerHir,
  Bind,
  TypeOfDef,
  CheckBody,
  Relation,
}

/// Aggregate statistics for a single query kind.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct QueryStat {
  pub total: u64,
  pub cache_hits: u64,
  pub cache_misses: u64,
  pub total_time_ms: f64,
  pub hit_rate: f64,
}

/// Summary of query statistics across all recorded kinds.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct QueryStats {
  pub queries: BTreeMap<QueryKind, QueryStat>,
}

#[derive(Debug, Clone, Default)]
struct QueryStatAccumulator {
  total: u64,
  cache_hits: u64,
  cache_misses: u64,
  total_time_ms: f64,
}

/// Internal collector shared by the checker to accumulate per-query metrics.
#[derive(Clone, Default)]
pub(crate) struct QueryStatsCollector {
  inner: Arc<Mutex<BTreeMap<QueryKind, QueryStatAccumulator>>>,
}

impl QueryStatsCollector {
  pub(crate) fn record(&self, kind: QueryKind, cache_hit: bool, duration: Duration) {
    let mut guard = self.inner.lock().unwrap();
    let entry = guard.entry(kind).or_default();
    entry.total += 1;
    if cache_hit {
      entry.cache_hits += 1;
    } else {
      entry.cache_misses += 1;
    }
    entry.total_time_ms += duration.as_secs_f64() * 1000.0;
  }

  pub(crate) fn snapshot(&self) -> QueryStats {
    let guard = self.inner.lock().unwrap();
    let mut queries = BTreeMap::new();
    for (kind, acc) in guard.iter() {
      queries.insert(
        *kind,
        QueryStat {
          total: acc.total,
          cache_hits: acc.cache_hits,
          cache_misses: acc.cache_misses,
          total_time_ms: acc.total_time_ms,
          hit_rate: if acc.total == 0 {
            0.0
          } else {
            acc.cache_hits as f64 / acc.total as f64
          },
        },
      );
    }
    QueryStats { queries }
  }
}

impl QueryStats {
  /// Merge another set of statistics into this one, summing counts and durations.
  pub fn merge(&mut self, other: &QueryStats) {
    for (kind, stat) in other.queries.iter() {
      let entry = self.queries.entry(*kind).or_default();
      entry.total += stat.total;
      entry.cache_hits += stat.cache_hits;
      entry.cache_misses += stat.cache_misses;
      entry.total_time_ms += stat.total_time_ms;
      entry.hit_rate = if entry.total == 0 {
        0.0
      } else {
        entry.cache_hits as f64 / entry.total as f64
      };
    }
  }

  pub fn is_empty(&self) -> bool {
    self.queries.is_empty()
  }
}
