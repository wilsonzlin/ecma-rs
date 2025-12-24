use serde::Serialize;
use std::env;
use std::hint::black_box;
use std::time::Duration;
use std::time::Instant;
use symbol_js::TopLevelMode;
use typecheck_ts_bench::fixtures::all_fixtures;
use typecheck_ts_bench::fixtures::module_graph_fixtures;
use typecheck_ts_bench::mini_types::assignability_stress;
use typecheck_ts_bench::mini_types::control_flow_body;
use typecheck_ts_bench::mini_types::generic_overload_body;
use typecheck_ts_bench::mini_types::union_intersection_body;
use typecheck_ts_bench::pipeline::bind_module_graph;
use typecheck_ts_bench::pipeline::bind_single_file;
use typecheck_ts_bench::pipeline::lower_to_hir;
use typecheck_ts_bench::pipeline::parse_only;

const PARSE_ITERS: u64 = 50;
const LOWER_ITERS: u64 = 120;
const BIND_ITERS: u64 = 40;
const CHECK_BODY_ITERS: u64 = 60;
const RELATIONS_ITERS: u64 = 80;

// To emit JSON alongside the human summary without tripping libtest argument
// parsing, set `TYPECHECK_TS_BENCH_JSON=1` in the environment. The `--json`
// flag is also accepted by this harness but will be forwarded to all test
// binaries by `cargo bench`.

const CONTROL_BODY_DEPTH: usize = 6;
const UNION_BODY_DEPTH: usize = 4;
const GENERIC_BODY_DEPTH: usize = 5;
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

  for fixture in all_fixtures() {
    results.push(measure(
      format!("parse/{}", fixture.name),
      PARSE_ITERS,
      || {
        let parsed = parse_only(fixture).expect("fixtures must parse");
        black_box(parsed.loc);
      },
    ));
  }

  for fixture in all_fixtures() {
    let parsed = parse_only(fixture).expect("fixtures must parse");
    results.push(measure(
      format!("lower/{}", fixture.name),
      LOWER_ITERS,
      || {
        let summary = lower_to_hir(&parsed);
        black_box(summary.node_count);
      },
    ));
  }

  for fixture in all_fixtures() {
    results.push(measure(
      format!("bind/{}", fixture.name),
      BIND_ITERS,
      || {
        let total = bind_single_file(fixture.source, TopLevelMode::Module);
        black_box(total);
      },
    ));
  }

  for graph in module_graph_fixtures() {
    results.push(measure(
      format!("bind/module_graph/{}", graph.name),
      BIND_ITERS,
      || {
        let total = bind_module_graph(graph);
        black_box(total);
      },
    ));
  }

  results.push(measure("check/control_flow", CHECK_BODY_ITERS, || {
    let stats = control_flow_body(CONTROL_BODY_DEPTH);
    black_box((stats.steps, stats.successes));
  }));

  results.push(measure("check/unions", CHECK_BODY_ITERS, || {
    let stats = union_intersection_body(UNION_BODY_DEPTH);
    black_box((stats.steps, stats.successes));
  }));

  results.push(measure("check/generics", CHECK_BODY_ITERS, || {
    let stats = generic_overload_body(GENERIC_BODY_DEPTH);
    black_box((stats.steps, stats.successes));
  }));

  results.push(measure("relations/cold", RELATIONS_ITERS, || {
    let stats = assignability_stress(RELATION_DEPTH, false);
    black_box((stats.steps, stats.successes));
  }));

  results.push(measure("relations/warm", RELATIONS_ITERS, || {
    let stats = assignability_stress(RELATION_DEPTH, true);
    black_box((stats.steps, stats.successes));
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
