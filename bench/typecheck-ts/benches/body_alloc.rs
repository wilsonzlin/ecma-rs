use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use typecheck_ts_bench::fixtures::all_fixtures;
use typecheck_ts_bench::pipeline::typecheck_fixture;

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
  let mut total_allocs = 0usize;
  let mut total_diags = 0usize;
  println!("=== allocation counts per fixture ===");
  for fixture in all_fixtures() {
    ALLOCATIONS.store(0, Ordering::Relaxed);
    let summary = typecheck_fixture(fixture);
    let allocs = ALLOCATIONS.load(Ordering::Relaxed);
    total_allocs += allocs;
    total_diags += summary.diagnostics;
    println!(
      "{:<24} allocations={:<10} diagnostics={}",
      fixture.name, allocs, summary.diagnostics
    );
  }
  println!(
    "{:<24} allocations={:<10} diagnostics={}",
    "total", total_allocs, total_diags
  );
}
