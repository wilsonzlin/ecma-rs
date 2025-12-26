use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use types_ts_interned::CacheStats as StoreCacheStats;

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

/// Buckets for cache statistics exposed by the checker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum CacheKind {
  Relation,
  Eval,
  RefExpansion,
  Instantiation,
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

/// Aggregate statistics for a cache.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct CacheStat {
  pub hits: u64,
  pub misses: u64,
  pub insertions: u64,
  pub evictions: u64,
  pub hit_rate: f64,
}

/// Summary of query statistics across all recorded kinds.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct QueryStats {
  pub queries: BTreeMap<QueryKind, QueryStat>,
  #[serde(default)]
  pub caches: BTreeMap<CacheKind, CacheStat>,
}

#[derive(Debug, Clone, Default)]
struct QueryStatAccumulator {
  total: u64,
  cache_hits: u64,
  cache_misses: u64,
  total_time_ms: f64,
}

#[derive(Debug, Clone, Default)]
struct CacheStatAccumulator {
  hits: u64,
  misses: u64,
  insertions: u64,
  evictions: u64,
}

/// Thread-safe accumulator shared by the checker and profiling harness to
/// record query timings and cache activity.
#[derive(Clone, Default)]
pub struct QueryStatsCollector {
  inner: Arc<Mutex<BTreeMap<QueryKind, QueryStatAccumulator>>>,
  caches: Arc<Mutex<BTreeMap<CacheKind, CacheStatAccumulator>>>,
}

impl QueryStatsCollector {
  pub fn record(&self, kind: QueryKind, cache_hit: bool, duration: Duration) {
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

  /// Merge cache statistics from a single cache snapshot into the collector.
  pub fn record_cache(&self, kind: CacheKind, stats: &StoreCacheStats) {
    let mut guard = self.caches.lock().unwrap();
    let entry = guard.entry(kind).or_default();
    entry.hits += stats.hits;
    entry.misses += stats.misses;
    entry.insertions += stats.insertions;
    entry.evictions += stats.evictions;
  }

  pub fn snapshot(&self) -> QueryStats {
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
    let cache_guard = self.caches.lock().unwrap();
    let mut caches = BTreeMap::new();
    for (kind, acc) in cache_guard.iter() {
      let lookups = acc.hits + acc.misses;
      caches.insert(
        *kind,
        CacheStat {
          hits: acc.hits,
          misses: acc.misses,
          insertions: acc.insertions,
          evictions: acc.evictions,
          hit_rate: if lookups == 0 {
            0.0
          } else {
            acc.hits as f64 / lookups as f64
          },
        },
      );
    }
    QueryStats { queries, caches }
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
    for (kind, stat) in other.caches.iter() {
      let entry = self.caches.entry(*kind).or_default();
      entry.hits += stat.hits;
      entry.misses += stat.misses;
      entry.insertions += stat.insertions;
      entry.evictions += stat.evictions;
      let lookups = entry.hits + entry.misses;
      entry.hit_rate = if lookups == 0 {
        0.0
      } else {
        entry.hits as f64 / lookups as f64
      };
    }
  }

  pub fn is_empty(&self) -> bool {
    self.queries.is_empty() && self.caches.is_empty()
  }
}
