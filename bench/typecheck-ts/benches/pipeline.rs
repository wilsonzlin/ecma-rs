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
use typecheck_ts_bench::pipeline::check_body_named;
use typecheck_ts_bench::pipeline::incremental_recheck;
use typecheck_ts_bench::pipeline::lower_to_hir;
use typecheck_ts_bench::pipeline::parse_and_lower;
use typecheck_ts_bench::pipeline::parse_only;
use typecheck_ts_bench::pipeline::summarize_hir;
use typecheck_ts_bench::pipeline::type_of_exported_defs;
use typecheck_ts_bench::pipeline::typecheck_fixture;
use typecheck_ts_bench::pipeline::typecheck_module_graph;
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
  let module_graphs = module_graph_fixtures();

  for fixture in fixtures {
    results.push(measure(
      format!("parse/{}", fixture.name),
      PARSE_ITERS,
      || {
        let parsed = parse_only(fixture)
          .unwrap_or_else(|err| panic!("fixtures must parse ({}): {err:?}", fixture.name));
        black_box(parsed.loc);
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
        let lowered = lower_to_hir(file_id, &parsed);
        let summary = summarize_hir(&lowered);
        black_box((summary.defs, summary.bodies, summary.exprs, summary.stmts));
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
      },
    ));
  }

  for graph in module_graphs {
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

  for graph in module_graphs {
    results.push(measure(
      format!("typecheck/module_graph/{}", graph.name),
      TYPECHECK_ITERS,
      || {
        let summary = typecheck_module_graph(graph);
        black_box((summary.bodies, summary.diagnostics));
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
  results.push(measure("check_body/generics", CHECK_BODY_ITERS, || {
    let summary = check_body_named(generics, "combine");
    black_box((summary.exprs, summary.diagnostics));
  }));

  if let Some(project) = module_graphs.iter().find(|g| g.name == "small_project") {
    let edit = IncrementalEdit {
      file: "project_text.ts",
      from: "const SEPARATOR = \":\";",
      to: "const SEPARATOR = \"-\";",
    };
    let mut full_total = Duration::ZERO;
    let mut edit_total = Duration::ZERO;
    for _ in 0..INCREMENTAL_ITERS {
      let timings = incremental_recheck(project, &edit);
      full_total += timings.full;
      edit_total += timings.edit;
      black_box((timings.full_diagnostics, timings.edit_diagnostics));
    }

    results.push(BenchResult {
      name: format!("incremental/full/{}", project.name),
      iterations: INCREMENTAL_ITERS,
      total_nanos: duration_to_nanos(full_total),
    });
    results.push(BenchResult {
      name: format!("incremental/edit/{}", project.name),
      iterations: INCREMENTAL_ITERS,
      total_nanos: duration_to_nanos(edit_total),
    });
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
