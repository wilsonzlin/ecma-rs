use diagnostics::FileId as HirFileId;
use serde::Serialize;
use std::env;
use std::hint::black_box;
use std::time::Duration;
use std::time::Instant;
use typecheck_ts_bench::fixtures::all_fixtures;
use typecheck_ts_bench::fixtures::module_graph_fixtures;
use typecheck_ts_bench::pipeline::assignability_micro;
use typecheck_ts_bench::pipeline::bind_module_graph;
use typecheck_ts_bench::pipeline::lower_to_hir;
use typecheck_ts_bench::pipeline::parse_only;
use typecheck_ts_bench::pipeline::summarize_hir;
use typecheck_ts_bench::pipeline::typecheck_fixture;
use typecheck_ts_bench::pipeline::typecheck_module_graph;

const PARSE_ITERS: u64 = 50;
const LOWER_ITERS: u64 = 120;
const BIND_ITERS: u64 = 40;
const TYPECHECK_ITERS: u64 = 40;
const RELATIONS_ITERS: u64 = 80;
const RELATION_DEPTH: usize = 6;

#[derive(Serialize)]
struct BenchResult {
  name: String,
  iterations: u64,
  total_nanos: u128,
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

fn main() {
  let args = BenchArgs::from_env();
  let mut results = Vec::new();

  let fixtures = all_fixtures();

  for fixture in fixtures {
    results.push(measure(
      format!("parse/{}", fixture.name),
      PARSE_ITERS,
      || {
        let parsed = parse_only(fixture).expect("fixtures must parse");
        black_box(parsed.loc);
      },
    ));
  }

  for (idx, fixture) in fixtures.iter().enumerate() {
    let parsed = parse_only(fixture).expect("fixtures must parse");
    let file_id = HirFileId(idx as u32);
    results.push(measure(
      format!("lower/{}", fixture.name),
      LOWER_ITERS,
      || {
        let lowered = lower_to_hir(file_id, &parsed);
        let summary = summarize_hir(&lowered);
        black_box((summary.defs, summary.bodies, summary.exprs, summary.stmts));
      },
    ));
  }

  for graph in module_graph_fixtures() {
    results.push(measure(
      format!("bind/module_graph/{}", graph.name),
      BIND_ITERS,
      || {
        let summary = bind_module_graph(graph);
        black_box((summary.exports, summary.globals, summary.diagnostics));
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
      },
    ));
  }

  for graph in module_graph_fixtures() {
    results.push(measure(
      format!("typecheck/module_graph/{}", graph.name),
      TYPECHECK_ITERS,
      || {
        let summary = typecheck_module_graph(graph);
        black_box((summary.bodies, summary.diagnostics));
      },
    ));
  }

  results.push(measure("relations/cold", RELATIONS_ITERS, || {
    let stats = assignability_micro(RELATION_DEPTH, false);
    black_box((stats.checks, stats.successes));
  }));

  results.push(measure("relations/warm", RELATIONS_ITERS, || {
    let stats = assignability_micro(RELATION_DEPTH, true);
    black_box((stats.checks, stats.successes));
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

fn measure(name: impl Into<String>, iterations: u64, mut f: impl FnMut()) -> BenchResult {
  let started = Instant::now();
  for _ in 0..iterations {
    f();
  }
  let total = started.elapsed();
  BenchResult {
    name: name.into(),
    iterations,
    total_nanos: duration_to_nanos(total),
  }
}

fn duration_to_nanos(dur: Duration) -> u128 {
  dur.as_secs() as u128 * 1_000_000_000u128 + dur.subsec_nanos() as u128
}

fn print_summary(results: &[BenchResult]) {
  println!("=== typecheck-ts benchmarks ===");
  for result in results {
    println!(
      "{:<32} {:>6} iters {:>12} ns ({:.2} ns/iter)",
      result.name,
      result.iterations,
      result.total_nanos,
      result.per_iter_ns(),
    );
  }
}
