use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use typecheck_ts_bench::fixtures::all_fixtures;
use typecheck_ts_bench::pipeline::check_body_named;

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

fn main() {
  let fixtures = all_fixtures();
  let targets = [
    ("control_flow", "evaluate"),
    ("unions", "area"),
    ("generics", "combine"),
    ("advanced_types", "mergeDefaults"),
    ("component_tsx", "Component"),
  ];

  println!("=== per-body check allocations ===");
  for (fixture_name, def) in targets {
    let fixture = fixtures
      .iter()
      .find(|f| f.name == fixture_name)
      .unwrap_or_else(|| panic!("missing fixture {fixture_name}"));
    ALLOCATIONS.store(0, Ordering::Relaxed);
    let summary = check_body_named(fixture, def);
    let allocs = ALLOCATIONS.load(Ordering::Relaxed);
    println!(
      "{:<16} {:<12} allocations={:<10} diagnostics={} exprs={}",
      fixture_name, def, allocs, summary.diagnostics, summary.exprs
    );
  }
}
