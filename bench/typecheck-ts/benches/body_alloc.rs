use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashSet;
use std::env;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::Serialize;
use typecheck_ts_bench::fixtures::all_fixtures;
use typecheck_ts_bench::pipeline::typecheck_fixture;

const SCHEMA_VERSION: u32 = 1;

struct CountingAlloc;

static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAlloc {
  unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
    ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
    System.alloc(layout)
  }

  unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
    System.dealloc(ptr, layout)
  }
}

#[global_allocator]
static GLOBAL: CountingAlloc = CountingAlloc;

#[derive(Clone, Debug, Serialize)]
struct AllocResult {
  name: String,
  allocations: u64,
  diagnostics: u64,
  #[serde(skip_serializing_if = "Option::is_none")]
  exprs: Option<u64>,
}

#[derive(Debug, Serialize)]
struct AllocReport {
  schema_version: u32,
  results: Vec<AllocResult>,
}

#[derive(Debug, Default)]
struct BenchArgs {
  json: bool,
  skip: bool,
  fixtures: Option<HashSet<String>>,
}

impl BenchArgs {
  fn from_env() -> Self {
    let mut args = BenchArgs::default();
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

    if let Ok(val) = env::var("TYPECHECK_TS_BENCH_ALLOC_SKIP") {
      if val == "1" || val.eq_ignore_ascii_case("true") {
        args.skip = true;
      }
    }

    if let Ok(val) = env::var("TYPECHECK_TS_BENCH_ALLOC_FIXTURES") {
      let selected = val
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(ToOwned::to_owned)
        .collect::<HashSet<_>>();
      if !selected.is_empty() {
        args.fixtures = Some(selected);
      }
    }

    args
  }
}

fn main() {
  let args = BenchArgs::from_env();
  let mut results = Vec::new();

  if args.skip {
    if args.json {
      eprintln!("=== allocation counts per fixture (skipped) ===");
      let report = AllocReport {
        schema_version: SCHEMA_VERSION,
        results,
      };
      println!(
        "{}",
        serde_json::to_string_pretty(&report).expect("json serialisation")
      );
    } else {
      println!("=== allocation counts per fixture (skipped) ===");
    }
    return;
  }

  let mut total_allocs = 0u64;
  let mut total_diags = 0u64;

  if args.json {
    eprintln!("=== allocation counts per fixture ===");
  } else {
    println!("=== allocation counts per fixture ===");
  }
  for fixture in all_fixtures() {
    if let Some(filter) = args.fixtures.as_ref() {
      if !filter.contains(fixture.name) {
        continue;
      }
    }
    ALLOCATIONS.store(0, Ordering::Relaxed);
    let summary = typecheck_fixture(fixture);
    let allocs = ALLOCATIONS.load(Ordering::Relaxed) as u64;
    let diags = summary.diagnostics as u64;
    total_allocs += allocs;
    total_diags += diags;

    results.push(AllocResult {
      name: fixture.name.to_string(),
      allocations: allocs,
      diagnostics: diags,
      exprs: None,
    });

    if args.json {
      eprintln!(
        "{:<24} allocations={:<10} diagnostics={}",
        fixture.name, allocs, summary.diagnostics
      );
    } else {
      println!(
        "{:<24} allocations={:<10} diagnostics={}",
        fixture.name, allocs, summary.diagnostics
      );
    }
  }

  if args.json {
    eprintln!(
      "{:<24} allocations={:<10} diagnostics={}",
      "total", total_allocs, total_diags
    );
    results.sort_by(|a, b| a.name.cmp(&b.name));
    let report = AllocReport {
      schema_version: SCHEMA_VERSION,
      results,
    };
    println!(
      "{}",
      serde_json::to_string_pretty(&report).expect("json serialisation")
    );
  } else {
    println!(
      "{:<24} allocations={:<10} diagnostics={}",
      "total", total_allocs, total_diags
    );
  }
}
