use diagnostics::FileId as HirFileId;
use serde::Serialize;
use std::collections::BTreeMap;
use std::env;
use std::hint::black_box;
use std::time::Duration;
use std::time::Instant;
use typecheck_ts::lib_support::{CacheMode, CacheOptions, CompilerOptions};
use typecheck_ts::CacheKind;
use typecheck_ts::QueryKind;
use typecheck_ts_bench::fixtures::{all_fixtures, module_graph_fixtures};
use typecheck_ts_bench::pipeline::{
  assignability_micro, bind_module_graph, check_body_with_warmups, hir_kind, incremental_recheck,
  lower_to_hir, parse_and_lower, parse_only, summarize_hir, type_of_exported_defs,
  typecheck_fixture, typecheck_module_graph, BodyCheckSummary, RelationStats, TypecheckSummary,
};
use typecheck_ts_bench::IncrementalEdit;

const PARSE_ITERS: u64 = 50;
const LOWER_ITERS: u64 = 120;
const PARSE_LOWER_ITERS: u64 = 40;
const BIND_ITERS: u64 = 40;
const TYPECHECK_ITERS: u64 = 40;
const TYPE_OF_DEF_ITERS: u64 = 40;
const CHECK_BODY_ITERS: u64 = 60;
const RELATIONS_ITERS: u64 = 80;
const RELATION_DEPTH: usize = 6;
const INCREMENTAL_ITERS: u64 = 10;

#[derive(Clone, Debug, Default, Serialize)]
struct BenchDetail {
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  counters: BTreeMap<String, u64>,
  #[serde(skip_serializing_if = "BTreeMap::is_empty")]
  metrics: BTreeMap<String, f64>,
}

impl BenchDetail {
  fn is_empty(&self) -> bool {
    self.counters.is_empty() && self.metrics.is_empty()
  }

  fn add_counter(&mut self, key: impl Into<String>, value: u64) {
    *self.counters.entry(key.into()).or_default() += value;
  }

  fn add_metric(&mut self, key: impl Into<String>, value: f64) {
    *self.metrics.entry(key.into()).or_default() += value;
  }

  fn merge(&mut self, other: BenchDetail) {
    for (key, value) in other.counters {
      *self.counters.entry(key).or_default() += value;
    }
    for (key, value) in other.metrics {
      *self.metrics.entry(key).or_default() += value;
    }
  }

  fn finalize(mut self, iterations: u64) -> Option<BenchDetail> {
    if let (Some(hits), Some(misses)) = (
      self.counters.get("relation_hits"),
      self.counters.get("relation_misses"),
    ) {
      let lookups = *hits + *misses;
      if lookups > 0 {
        self.metrics.insert(
          "relation_hit_rate".to_string(),
          *hits as f64 / lookups as f64,
        );
      }
    }
    if iterations > 0 {
      let iter_f = iterations as f64;
      for (key, value) in self.metrics.iter_mut() {
        if !key.ends_with("_rate") {
          *value /= iter_f;
        }
      }
    }
    if self.is_empty() {
      None
    } else {
      Some(self)
    }
  }
}

#[derive(Serialize)]
struct BenchResult {
  name: String,
  iterations: u64,
  total_nanos: u128,
  #[serde(skip_serializing_if = "Option::is_none")]
  details: Option<BenchDetail>,
}

impl BenchResult {
  fn per_iter_ns(&self) -> f64 {
    self.total_nanos as f64 / self.iterations as f64
  }
}

#[derive(Default)]
struct BenchArgs {
  json: bool,
}

impl BenchArgs {
  fn from_env() -> Self {
    let mut args = BenchArgs { json: false };
    for arg in env::args().skip(1) {
      if arg == "--json" {
        args.json = true;
      }
    }

    if let Ok(val) = env::var("TYPECHECK_TS_BENCH_JSON") {
      if val == "1" || val.eq_ignore_ascii_case("true") {
        args.json = true;
      }
    }
    args
  }
}

fn detail_from_typecheck(summary: &TypecheckSummary) -> BenchDetail {
  let mut detail = detail_from_query_stats(&summary.stats);
  detail.add_counter("diagnostics", summary.diagnostics as u64);
  detail.add_counter("bodies", summary.bodies as u64);
  detail
}

fn detail_from_body(summary: &BodyCheckSummary) -> BenchDetail {
  let mut detail = detail_from_query_stats(&summary.stats);
  detail.add_counter("diagnostics", summary.diagnostics as u64);
  detail.add_counter("exprs", summary.exprs as u64);
  detail
}

fn detail_from_relation(stats: &RelationStats) -> BenchDetail {
  let mut detail = BenchDetail::default();
  detail.add_counter("relation_checks", stats.checks as u64);
  detail.add_counter("relation_successes", stats.successes as u64);
  detail.add_counter("relation_hits", stats.cache.hits);
  detail.add_counter("relation_misses", stats.cache.misses);
  detail.add_counter("relation_evictions", stats.cache.evictions);
  detail.add_counter("relation_insertions", stats.cache.insertions);
  detail
}

fn detail_from_query_stats(stats: &typecheck_ts::QueryStats) -> BenchDetail {
  let mut detail = BenchDetail::default();
  if let Some(parse) = stats.queries.get(&QueryKind::Parse) {
    detail.add_metric("parse_ms", parse.total_time_ms);
  }
  if let Some(lower) = stats.queries.get(&QueryKind::LowerHir) {
    detail.add_metric("lower_ms", lower.total_time_ms);
  }
  if let Some(bind) = stats.queries.get(&QueryKind::Bind) {
    detail.add_metric("bind_ms", bind.total_time_ms);
  }
  if let Some(check_body) = stats.queries.get(&QueryKind::CheckBody) {
    detail.add_metric("check_body_ms", check_body.total_time_ms);
    detail.add_counter("check_body_count", check_body.total);
  }
  if let Some(relation) = stats.caches.get(&CacheKind::Relation) {
    detail.add_counter("relation_hits", relation.hits);
    detail.add_counter("relation_misses", relation.misses);
    detail.add_counter("relation_evictions", relation.evictions);
    detail.add_counter("relation_insertions", relation.insertions);
  }
  detail
}

fn main() {
  let args = BenchArgs::from_env();
  let mut results = Vec::new();

  let fixtures = all_fixtures();
  let module_graphs = module_graph_fixtures();
  let mut cold_cache_options = CompilerOptions::default();
  cold_cache_options.cache = CacheOptions {
    mode: CacheMode::PerBody,
    ..CacheOptions::default()
  };

  for fixture in fixtures {
    results.push(measure(
      format!("parse/{}", fixture.name),
      PARSE_ITERS,
      || {
        let parsed = parse_only(fixture)
          .unwrap_or_else(|err| panic!("fixtures must parse ({}): {err:?}", fixture.name));
        black_box(parsed.loc);
        BenchDetail::default()
      },
    ));
  }

  for (idx, fixture) in fixtures.iter().enumerate() {
    let parsed = parse_only(fixture)
      .unwrap_or_else(|err| panic!("fixtures must parse ({}): {err:?}", fixture.name));
    let file_id = HirFileId(idx as u32);
    results.push(measure(
      format!("lower/{}", fixture.name),
      LOWER_ITERS,
      || {
        let lowered = lower_to_hir(file_id, hir_kind(fixture.kind), &parsed);
        let summary = summarize_hir(&lowered);
        black_box((summary.defs, summary.bodies, summary.exprs, summary.stmts));
        BenchDetail::default()
      },
    ));
  }

  for (idx, fixture) in fixtures.iter().enumerate() {
    let file_id = HirFileId(idx as u32);
    results.push(measure(
      format!("parse_lower/{}", fixture.name),
      PARSE_LOWER_ITERS,
      || {
        let summary = parse_and_lower(file_id, fixture);
        black_box((summary.defs, summary.bodies, summary.exprs, summary.stmts));
        BenchDetail::default()
      },
    ));
  }

  for graph in module_graphs {
    results.push(measure(
      format!("pipeline/parse_lower_bind/{}", graph.name),
      BIND_ITERS,
      || {
        let summary = bind_module_graph(graph);
        black_box((summary.exports, summary.globals, summary.diagnostics));
        let mut detail = BenchDetail::default();
        detail.add_counter("exports", summary.exports as u64);
        detail.add_counter("globals", summary.globals as u64);
        detail.add_counter("diagnostics", summary.diagnostics as u64);
        detail
      },
    ));
  }

  for fixture in fixtures {
    results.push(measure(
      format!("typecheck/{}", fixture.name),
      TYPECHECK_ITERS,
      || {
        let summary = typecheck_fixture(fixture);
        black_box((summary.bodies, summary.diagnostics));
        detail_from_typecheck(&summary)
      },
    ));
  }

  for graph in module_graphs {
    results.push(measure(
      format!("typecheck/module_graph/{}", graph.name),
      TYPECHECK_ITERS,
      || {
        let summary = typecheck_module_graph(graph);
        black_box((summary.bodies, summary.diagnostics));
        detail_from_typecheck(&summary)
      },
    ));
  }

  for graph in module_graphs {
    results.push(measure(
      format!("type_of_def/exports/{}", graph.name),
      TYPE_OF_DEF_ITERS,
      || {
        let summary = type_of_exported_defs(graph);
        black_box((summary.exports, summary.rendered_types.len()));
        let mut detail = BenchDetail::default();
        detail.add_counter("exports", summary.exports as u64);
        detail
      },
    ));
  }

  let control_flow = fixtures
    .iter()
    .find(|f| f.name == "control_flow")
    .expect("control_flow fixture");
  results.push(measure("check_body/control_flow", CHECK_BODY_ITERS, || {
    let summary = check_body_named(control_flow, "evaluate");
    black_box((summary.exprs, summary.diagnostics));
  }));

  let generics = fixtures
    .iter()
    .find(|f| f.name == "generics")
    .expect("generics fixture");
  let advanced = fixtures
    .iter()
    .find(|f| f.name == "advanced_types")
    .expect("advanced_types fixture");
  results.push(measure(
    "check_body/cold/control_flow",
    CHECK_BODY_ITERS,
    || {
      let summary =
        check_body_with_warmups((control_flow, "evaluate"), &[], cold_cache_options.clone());
      black_box((summary.exprs, summary.diagnostics));
      detail_from_body(&summary)
    },
  ));

  results.push(measure(
    "check_body/warm/control_flow",
    CHECK_BODY_ITERS,
    || {
      let summary = check_body_with_warmups(
        (control_flow, "evaluate"),
        &[(generics, "combine")],
        CompilerOptions::default(),
      );
      black_box((summary.exprs, summary.diagnostics));
      detail_from_body(&summary)
    },
  ));

  results.push(measure(
    "check_body/cold/advanced_types",
    CHECK_BODY_ITERS,
    || {
      let summary =
        check_body_with_warmups((advanced, "mergeDefaults"), &[], cold_cache_options.clone());
      black_box((summary.exprs, summary.diagnostics));
      detail_from_body(&summary)
    },
  ));

  results.push(measure(
    "check_body/warm/advanced_types",
    CHECK_BODY_ITERS,
    || {
      let summary = check_body_with_warmups(
        (advanced, "mergeDefaults"),
        &[(control_flow, "evaluate"), (generics, "combine")],
        CompilerOptions::default(),
      );
      black_box((summary.exprs, summary.diagnostics));
      detail_from_body(&summary)
    },
  ));

  if let Some(project) = module_graphs.iter().find(|g| g.name == "small_project") {
    let edit = IncrementalEdit {
      file: "project_text.ts",
      from: "const SEPARATOR = \":\";",
      to: "const SEPARATOR = \"-\";",
    };
    let mut full_total = Duration::ZERO;
    let mut edit_total = Duration::ZERO;
    let mut full_detail = BenchDetail::default();
    let mut edit_detail = BenchDetail::default();
    for _ in 0..INCREMENTAL_ITERS {
      let timings = incremental_recheck(project, &edit);
      full_total += timings.full;
      edit_total += timings.edit;
      full_detail.merge(detail_from_typecheck(&timings.full_summary));
      edit_detail.merge(detail_from_typecheck(&timings.edit_summary));
      black_box((
        timings.full_summary.diagnostics,
        timings.edit_summary.diagnostics,
      ));
    }

    results.push(BenchResult {
      name: format!("incremental/full/{}", project.name),
      iterations: INCREMENTAL_ITERS,
      total_nanos: duration_to_nanos(full_total),
      details: full_detail.finalize(INCREMENTAL_ITERS),
    });
    results.push(BenchResult {
      name: format!("incremental/edit/{}", project.name),
      iterations: INCREMENTAL_ITERS,
      total_nanos: duration_to_nanos(edit_total),
      details: edit_detail.finalize(INCREMENTAL_ITERS),
    });
  }

  results.push(measure("relations/cold", RELATIONS_ITERS, || {
    let stats = assignability_micro(RELATION_DEPTH, false);
    black_box((stats.checks, stats.successes));
    detail_from_relation(&stats)
  }));

  results.push(measure("relations/warm", RELATIONS_ITERS, || {
    let stats = assignability_micro(RELATION_DEPTH, true);
    black_box((stats.checks, stats.successes));
    detail_from_relation(&stats)
  }));

  print_summary(&results);

  if args.json {
    let json = serde_json::json!({ "benches": results });
    println!(
      "{}",
      serde_json::to_string_pretty(&json).expect("json serialisation")
    );
  }
}

fn measure(
  name: impl Into<String>,
  iterations: u64,
  mut f: impl FnMut() -> BenchDetail,
) -> BenchResult {
  let mut detail = BenchDetail::default();
  let started = Instant::now();
  for _ in 0..iterations {
    detail.merge(f());
  }
  let total = started.elapsed();
  BenchResult {
    name: name.into(),
    iterations,
    total_nanos: duration_to_nanos(total),
    details: detail.finalize(iterations),
  }
}

fn duration_to_nanos(dur: Duration) -> u128 {
  dur.as_secs() as u128 * 1_000_000_000u128 + dur.subsec_nanos() as u128
}

fn print_summary(results: &[BenchResult]) {
  println!("=== typecheck-ts benchmarks ===");
  for result in results {
    let detail = result
      .details
      .as_ref()
      .and_then(|d| format_detail(d, result.iterations));
    if let Some(detail) = detail {
      println!(
        "{:<32} {:>6} iters {:>12} ns ({:.2} ns/iter) {}",
        result.name,
        result.iterations,
        result.total_nanos,
        result.per_iter_ns(),
        detail,
      );
    } else {
      println!(
        "{:<32} {:>6} iters {:>12} ns ({:.2} ns/iter)",
        result.name,
        result.iterations,
        result.total_nanos,
        result.per_iter_ns(),
      );
    }
  }
}

fn format_detail(detail: &BenchDetail, iterations: u64) -> Option<String> {
  let mut parts = Vec::new();
  let iter = iterations.max(1);
  if let Some(diags) = detail.counters.get("diagnostics") {
    parts.push(format!("diagnostics/iter={}", diags / iter));
  }
  if let Some(exports) = detail.counters.get("exports") {
    parts.push(format!("exports/iter={}", exports / iter));
  }
  if let Some(globals) = detail.counters.get("globals") {
    parts.push(format!("globals/iter={}", globals / iter));
  }
  if let Some(bodies) = detail.counters.get("bodies") {
    parts.push(format!("bodies/iter={}", bodies / iter));
  }
  if let Some(exprs) = detail.counters.get("exprs") {
    parts.push(format!("exprs/iter={}", exprs / iter));
  }
  if let Some(body_checks) = detail.counters.get("check_body_count") {
    parts.push(format!("checked_bodies/iter={}", body_checks / iter));
  }
  if let Some(checks) = detail.counters.get("relation_checks") {
    let successes = detail
      .counters
      .get("relation_successes")
      .copied()
      .unwrap_or(0);
    parts.push(format!("relation_checks={checks} successes={successes}"));
  }
  if let Some(hit_rate) = detail.metrics.get("relation_hit_rate") {
    parts.push(format!("relation_hit_rate={:.2}%", hit_rate * 100.0));
  }
  for stage in ["parse_ms", "lower_ms", "bind_ms", "check_body_ms"] {
    if let Some(ms) = detail.metrics.get(stage) {
      parts.push(format!("{stage}={:.2}ms/iter", ms));
    }
  }
  if let Some(insertions) = detail.counters.get("relation_insertions") {
    if *insertions > 0 {
      parts.push(format!("relation_insertions={insertions}"));
    }
  }
  if parts.is_empty() {
    None
  } else {
    Some(parts.join(" "))
  }
}
