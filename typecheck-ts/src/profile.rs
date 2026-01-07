use dashmap::DashMap;
use salsa::{DatabaseKeyIndex, Event, EventKind};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread::ThreadId;
use std::time::{Duration, Instant};
use types_ts_interned::CacheStats as StoreCacheStats;

/// Named query boundaries used for tracing and profiling.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum QueryKind {
  Parse,
  LowerHir,
  Bind,
  TypeOfDef,
  BuildBodyContext,
  CheckBody,
  Relation,
}

impl QueryKind {
  pub const ALL: [QueryKind; 7] = [
    QueryKind::Parse,
    QueryKind::LowerHir,
    QueryKind::Bind,
    QueryKind::TypeOfDef,
    QueryKind::BuildBodyContext,
    QueryKind::CheckBody,
    QueryKind::Relation,
  ];

  pub const COUNT: usize = QueryKind::ALL.len();

  #[inline]
  pub fn index(self) -> usize {
    match self {
      QueryKind::Parse => 0,
      QueryKind::LowerHir => 1,
      QueryKind::Bind => 2,
      QueryKind::TypeOfDef => 3,
      QueryKind::BuildBodyContext => 4,
      QueryKind::CheckBody => 5,
      QueryKind::Relation => 6,
    }
  }
}

/// Buckets for cache statistics exposed by the checker.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CacheKind {
  Relation,
  Eval,
  RefExpansion,
  Instantiation,
  Body,
  Def,
}

impl CacheKind {
  pub const ALL: [CacheKind; 6] = [
    CacheKind::Relation,
    CacheKind::Eval,
    CacheKind::RefExpansion,
    CacheKind::Instantiation,
    CacheKind::Body,
    CacheKind::Def,
  ];

  pub const COUNT: usize = CacheKind::ALL.len();

  #[inline]
  pub fn index(self) -> usize {
    match self {
      CacheKind::Relation => 0,
      CacheKind::Eval => 1,
      CacheKind::RefExpansion => 2,
      CacheKind::Instantiation => 3,
      CacheKind::Body => 4,
      CacheKind::Def => 5,
    }
  }
}

/// Aggregate statistics for a single query kind.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Default)]
pub struct QueryStat {
  pub total: u64,
  pub cache_hits: u64,
  pub cache_misses: u64,
  pub total_time_ms: f64,
  pub hit_rate: f64,
}

/// Aggregate statistics for a cache.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Default)]
pub struct CacheStat {
  pub hits: u64,
  pub misses: u64,
  pub insertions: u64,
  pub evictions: u64,
  pub hit_rate: f64,
}

/// Summary of query statistics across all recorded kinds.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Default)]
pub struct QueryStats {
  pub queries: BTreeMap<QueryKind, QueryStat>,
  #[cfg_attr(feature = "serde", serde(default))]
  pub caches: BTreeMap<CacheKind, CacheStat>,
}

#[derive(Debug, Clone, Default)]
struct QueryStatAccumulator {
  total: u64,
  cache_hits: u64,
  cache_misses: u64,
  total_time_ns: u128,
}

#[derive(Debug, Clone, Default)]
struct CacheStatAccumulator {
  hits: u64,
  misses: u64,
  insertions: u64,
  evictions: u64,
}

#[derive(Debug, Default)]
struct QueryCounters {
  total: AtomicU64,
  cache_hits: AtomicU64,
  cache_misses: AtomicU64,
  total_time_ns: AtomicU64,
  recorded: AtomicBool,
}

impl QueryCounters {
  fn record(&self, cache_hit: bool, duration: Duration) {
    self.total.fetch_add(1, Ordering::Relaxed);
    if cache_hit {
      self.cache_hits.fetch_add(1, Ordering::Relaxed);
    } else {
      self.cache_misses.fetch_add(1, Ordering::Relaxed);
    }
    let nanos = duration.as_nanos().min(u64::MAX as u128) as u64;
    self.total_time_ns.fetch_add(nanos, Ordering::Relaxed);
    self.recorded.store(true, Ordering::Relaxed);
  }

  fn snapshot(&self) -> (QueryStatAccumulator, bool) {
    let total = self.total.load(Ordering::Relaxed);
    let cache_hits = self.cache_hits.load(Ordering::Relaxed);
    let cache_misses = self.cache_misses.load(Ordering::Relaxed);
    let total_time_ns = self.total_time_ns.load(Ordering::Relaxed) as u128;
    let recorded = self.recorded.load(Ordering::Relaxed);
    (
      QueryStatAccumulator {
        total,
        cache_hits,
        cache_misses,
        total_time_ns,
      },
      recorded || total > 0 || cache_hits > 0 || cache_misses > 0 || total_time_ns > 0,
    )
  }
}

#[derive(Debug, Default)]
struct CacheCounters {
  hits: AtomicU64,
  misses: AtomicU64,
  insertions: AtomicU64,
  evictions: AtomicU64,
  recorded: AtomicBool,
}

impl CacheCounters {
  fn record(&self, stats: &StoreCacheStats) {
    self.hits.fetch_add(stats.hits, Ordering::Relaxed);
    self.misses.fetch_add(stats.misses, Ordering::Relaxed);
    self
      .insertions
      .fetch_add(stats.insertions, Ordering::Relaxed);
    self.evictions.fetch_add(stats.evictions, Ordering::Relaxed);
    self.recorded.store(true, Ordering::Relaxed);
  }

  fn snapshot(&self) -> (CacheStatAccumulator, bool) {
    let hits = self.hits.load(Ordering::Relaxed);
    let misses = self.misses.load(Ordering::Relaxed);
    let insertions = self.insertions.load(Ordering::Relaxed);
    let evictions = self.evictions.load(Ordering::Relaxed);
    let recorded = self.recorded.load(Ordering::Relaxed);
    (
      CacheStatAccumulator {
        hits,
        misses,
        insertions,
        evictions,
      },
      recorded || hits > 0 || misses > 0 || insertions > 0 || evictions > 0,
    )
  }
}

#[derive(Debug)]
struct ThreadStats {
  queries: [QueryCounters; QueryKind::COUNT],
  caches: [CacheCounters; CacheKind::COUNT],
}

impl Default for ThreadStats {
  fn default() -> Self {
    ThreadStats {
      queries: QueryKind::ALL.map(|_| QueryCounters::default()),
      caches: CacheKind::ALL.map(|_| CacheCounters::default()),
    }
  }
}

#[derive(Debug)]
struct CollectorInner {
  id: usize,
  threads: DashMap<ThreadId, Arc<ThreadStats>>,
}

impl CollectorInner {
  fn new() -> Self {
    static NEXT_COLLECTOR_ID: AtomicUsize = AtomicUsize::new(1);
    CollectorInner {
      id: NEXT_COLLECTOR_ID.fetch_add(1, Ordering::Relaxed),
      threads: DashMap::new(),
    }
  }
}

thread_local! {
  static LOCAL_STATS: RefCell<HashMap<usize, Arc<ThreadStats>>> = RefCell::new(HashMap::new());
}

/// Thread-safe accumulator shared by the checker and profiling harness to
/// record query timings and cache activity. Stats are sharded per thread to
/// avoid contending on a single global lock during parallel execution.
#[derive(Clone)]
pub struct QueryStatsCollector {
  inner: Arc<CollectorInner>,
}

impl Default for QueryStatsCollector {
  fn default() -> Self {
    QueryStatsCollector {
      inner: Arc::new(CollectorInner::new()),
    }
  }
}

impl QueryStatsCollector {
  fn thread_stats(&self) -> Arc<ThreadStats> {
    LOCAL_STATS.with(|local| {
      let mut local = local.borrow_mut();
      if let Some(existing) = local.get(&self.inner.id) {
        return existing.clone();
      }
      let stats = Arc::new(ThreadStats::default());
      self
        .inner
        .threads
        .insert(std::thread::current().id(), stats.clone());
      local.insert(self.inner.id, stats.clone());
      stats
    })
  }

  pub fn record(&self, kind: QueryKind, cache_hit: bool, duration: Duration) {
    let stats = self.thread_stats();
    let counters = &stats.queries[kind.index()];
    counters.record(cache_hit, duration);
  }

  /// Merge cache statistics from a single cache snapshot into the collector.
  pub fn record_cache(&self, kind: CacheKind, stats: &StoreCacheStats) {
    let thread_stats = self.thread_stats();
    let counters = &thread_stats.caches[kind.index()];
    counters.record(stats);
  }

  /// Start a new timer that will record a query duration when dropped.
  pub fn timer(&self, kind: QueryKind, cache_hit: bool) -> QueryTimer {
    QueryTimer::new(self.clone(), kind, cache_hit)
  }

  /// Start a new timer using an explicit start instant. Useful when the caller
  /// already captured a timestamp (e.g. from salsa events).
  pub fn timer_with_start(&self, kind: QueryKind, cache_hit: bool, start: Instant) -> QueryTimer {
    QueryTimer::with_start(self.clone(), kind, cache_hit, start)
  }

  pub fn snapshot(&self) -> QueryStats {
    let mut query_accums = QueryKind::ALL.map(|_| QueryStatAccumulator::default());
    let mut cache_accums = CacheKind::ALL.map(|_| CacheStatAccumulator::default());
    let mut query_present = QueryKind::ALL.map(|_| false);
    let mut cache_present = CacheKind::ALL.map(|_| false);

    for stats in self.inner.threads.iter() {
      let stats = stats.value();
      for (idx, counters) in stats.queries.iter().enumerate() {
        let (snapshot, recorded) = counters.snapshot();
        query_present[idx] |= recorded;
        query_accums[idx].total += snapshot.total;
        query_accums[idx].cache_hits += snapshot.cache_hits;
        query_accums[idx].cache_misses += snapshot.cache_misses;
        query_accums[idx].total_time_ns += snapshot.total_time_ns;
      }
      for (idx, counters) in stats.caches.iter().enumerate() {
        let (snapshot, recorded) = counters.snapshot();
        cache_present[idx] |= recorded;
        cache_accums[idx].hits += snapshot.hits;
        cache_accums[idx].misses += snapshot.misses;
        cache_accums[idx].insertions += snapshot.insertions;
        cache_accums[idx].evictions += snapshot.evictions;
      }
    }

    let mut queries = BTreeMap::new();
    for (idx, kind) in QueryKind::ALL.iter().enumerate() {
      if !query_present[idx] {
        continue;
      }
      let acc = &query_accums[idx];
      queries.insert(
        *kind,
        QueryStat {
          total: acc.total,
          cache_hits: acc.cache_hits,
          cache_misses: acc.cache_misses,
          total_time_ms: acc.total_time_ns as f64 / 1_000_000.0,
          hit_rate: if acc.total == 0 {
            0.0
          } else {
            acc.cache_hits as f64 / acc.total as f64
          },
        },
      );
    }

    let mut caches = BTreeMap::new();
    for (idx, kind) in CacheKind::ALL.iter().enumerate() {
      if !cache_present[idx] {
        continue;
      }
      let acc = &cache_accums[idx];
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

/// RAII helper that records a single query duration into a
/// [`QueryStatsCollector`] when dropped.
#[derive(Clone)]
pub struct QueryTimer {
  collector: QueryStatsCollector,
  kind: QueryKind,
  cache_hit: bool,
  start: Instant,
  finished: bool,
}

impl QueryTimer {
  pub fn new(collector: QueryStatsCollector, kind: QueryKind, cache_hit: bool) -> Self {
    QueryTimer {
      collector,
      kind,
      cache_hit,
      start: Instant::now(),
      finished: false,
    }
  }

  pub fn with_start(
    collector: QueryStatsCollector,
    kind: QueryKind,
    cache_hit: bool,
    start: Instant,
  ) -> Self {
    QueryTimer {
      collector,
      kind,
      cache_hit,
      start,
      finished: false,
    }
  }

  /// Explicitly finish the timer with the provided duration. Dropping the timer
  /// without calling this will record using the elapsed time since creation.
  pub fn finish_with_duration(mut self, duration: Duration) {
    if self.finished {
      return;
    }
    self.collector.record(self.kind, self.cache_hit, duration);
    self.finished = true;
  }
}

impl Drop for QueryTimer {
  fn drop(&mut self) {
    if self.finished {
      return;
    }
    let duration = self.start.elapsed();
    self.collector.record(self.kind, self.cache_hit, duration);
    self.finished = true;
  }
}

/// Adapter that bridges salsa query events into the existing profiling
/// collector. Cache hits are recorded from `DidValidateMemoizedValue` events,
/// while [`QueryTimer`]s can be requested when a query executes to record
/// durations without adding contention.
#[derive(Clone)]
pub struct SalsaEventAdapter {
  collector: QueryStatsCollector,
  mapper: Arc<dyn Fn(DatabaseKeyIndex) -> Option<QueryKind> + Send + Sync>,
  starts: DashMap<DatabaseKeyIndex, (QueryKind, Instant)>,
}

impl SalsaEventAdapter {
  pub fn new(
    collector: QueryStatsCollector,
    mapper: impl Fn(DatabaseKeyIndex) -> Option<QueryKind> + Send + Sync + 'static,
  ) -> Self {
    SalsaEventAdapter {
      collector,
      mapper: Arc::new(mapper),
      starts: DashMap::default(),
    }
  }

  /// Handle a salsa event emitted from [`salsa::Database::salsa_event`]. Cache
  /// hits are recorded immediately. `WillExecute` events register a start time
  /// so the eventual query body can retrieve a [`QueryTimer`] with
  /// [`SalsaEventAdapter::start_query`].
  pub fn on_event(&self, event: &Event) {
    match &event.kind {
      EventKind::DidValidateMemoizedValue { database_key } => {
        if let Some(kind) = (self.mapper)(*database_key) {
          self.collector.record(kind, true, Duration::ZERO);
        }
      }
      EventKind::WillExecute { database_key } => {
        if let Some(kind) = (self.mapper)(*database_key) {
          self.starts.insert(*database_key, (kind, Instant::now()));
        }
      }
      _ => {}
    }
  }

  /// Obtain a query timer for an executing salsa query. This should be called
  /// from inside the query function; it reuses the start time recorded from the
  /// corresponding `WillExecute` event when available.
  pub fn start_query(&self, key: DatabaseKeyIndex) -> Option<QueryTimer> {
    let now = Instant::now();
    let (kind, start) = self
      .starts
      .remove(&key)
      .map(|(_, data)| data)
      .or_else(|| (self.mapper)(key).map(|kind| (kind, now)))?;
    Some(QueryTimer::with_start(
      self.collector.clone(),
      kind,
      false,
      start,
    ))
  }

  /// Access the underlying collector for custom timing.
  pub fn collector(&self) -> QueryStatsCollector {
    self.collector.clone()
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
