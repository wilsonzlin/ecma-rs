use std::sync::Arc;
use std::thread;
use std::time::Duration;

use typecheck_ts::{CacheKind, FileKey, MemoryHost, Program, QueryKind, QueryStatsCollector};
use types_ts_interned::CacheStats;

#[test]
fn query_stats_aggregate_across_threads() {
  let collector = QueryStatsCollector::default();
  let threads = 8usize;
  let iterations = 256u64;

  let handles: Vec<_> = (0..threads)
    .map(|i| {
      let collector = collector.clone();
      thread::spawn(move || {
        for _ in 0..iterations {
          collector.record(QueryKind::CheckBody, true, Duration::from_millis(1));
          collector.record(QueryKind::Relation, false, Duration::from_millis(2));
        }
        let cache_stats = CacheStats {
          hits: i as u64 + 1,
          misses: iterations,
          insertions: 0,
          evictions: 0,
        };
        collector.record_cache(CacheKind::Eval, &cache_stats);
      })
    })
    .collect();

  for handle in handles {
    handle.join().expect("thread panicked");
  }

  let stats = collector.snapshot();

  let check_body = stats
    .queries
    .get(&QueryKind::CheckBody)
    .cloned()
    .expect("missing check body stats");
  let relation = stats
    .queries
    .get(&QueryKind::Relation)
    .cloned()
    .expect("missing relation stats");

  assert_eq!(check_body.total, threads as u64 * iterations);
  assert_eq!(check_body.cache_hits, check_body.total);
  assert_eq!(relation.total, threads as u64 * iterations);
  assert_eq!(relation.cache_misses, relation.total);
  assert!(
    (check_body.total_time_ms - (threads as u64 * iterations) as f64).abs() < 1e-6,
    "unexpected check_body total_time_ms {}",
    check_body.total_time_ms
  );
  assert!(
    (relation.total_time_ms - (threads as u64 * iterations * 2) as f64).abs() < 1e-6,
    "unexpected relation total_time_ms {}",
    relation.total_time_ms
  );

  let eval = stats
    .caches
    .get(&CacheKind::Eval)
    .cloned()
    .expect("missing eval cache stats");
  let expected_hits: u64 = (0..threads).map(|i| i as u64 + 1).sum();
  assert_eq!(eval.hits, expected_hits);
  assert_eq!(eval.misses, threads as u64 * iterations);

  let query_keys: Vec<_> = stats.queries.keys().copied().collect();
  let mut sorted_query_keys = query_keys.clone();
  sorted_query_keys.sort();
  assert_eq!(
    query_keys, sorted_query_keys,
    "query keys should be deterministic"
  );

  let cache_keys: Vec<_> = stats.caches.keys().copied().collect();
  let mut sorted_cache_keys = cache_keys.clone();
  sorted_cache_keys.sort();
  assert_eq!(
    cache_keys, sorted_cache_keys,
    "cache keys should be deterministic"
  );
}

#[test]
fn program_records_query_stats_after_check() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("index.ts");
  host.insert(
    file.clone(),
    "export function add(a: number, b: number) { return a + b; }",
  );
  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "unexpected diagnostics {diagnostics:?}");

  let stats = program.query_stats();
  for kind in [
    QueryKind::Parse,
    QueryKind::LowerHir,
    QueryKind::CheckBody,
    QueryKind::TypeOfDef,
  ] {
    let entry = stats.queries.get(&kind).cloned().unwrap_or_default();
    assert!(
      entry.total > 0,
      "expected stats for {kind:?} to be recorded"
    );
  }
}

#[test]
fn salsa_events_feed_collector() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("index.ts");
  host.insert(file.clone(), "export const x = 1;");
  let program = Program::new(host, vec![file]);

  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics from ts_semantics: {:?}",
    diagnostics
  );

  let snapshot = program.query_stats();
  for kind in [QueryKind::Parse, QueryKind::LowerHir, QueryKind::Bind] {
    let entry = snapshot.queries.get(&kind).cloned().unwrap_or_default();
    assert!(entry.total > 0, "{kind:?} stat should be recorded");
  }
}
