use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::mem;
use vm_js::{Heap, HeapLimits, Value, VmError};

// These tests use a counting allocator to detect large, unexpected allocations inside
// `Heap::symbol_for`. In particular, cloning a `JsString` for use as a map key would allocate a
// second copy of the UTF-16 buffer. That isn't tracked by `Heap::used_bytes()`, so we measure host
// allocations directly.
thread_local! {
  static ALLOCATED_BYTES: Cell<usize> = Cell::new(0);
}

struct CountingAlloc;

#[global_allocator]
static GLOBAL_ALLOCATOR: CountingAlloc = CountingAlloc;

unsafe impl GlobalAlloc for CountingAlloc {
  unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
    let ptr = System.alloc(layout);
    if !ptr.is_null() {
      ALLOCATED_BYTES.with(|bytes| {
        bytes.set(bytes.get().saturating_add(layout.size()));
      });
    }
    ptr
  }

  unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
    System.dealloc(ptr, layout);
  }

  unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
    let ptr = System.realloc(ptr, layout, new_size);
    if !ptr.is_null() {
      ALLOCATED_BYTES.with(|bytes| {
        bytes.set(bytes.get().saturating_add(new_size));
      });
    }
    ptr
  }
}

fn reset_allocated_bytes() {
  ALLOCATED_BYTES.with(|bytes| bytes.set(0));
}

fn allocated_bytes() -> usize {
  ALLOCATED_BYTES.with(|bytes| bytes.get())
}

#[test]
fn symbol_for_returns_same_symbol_for_two_different_strings_with_same_contents() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let key_a = scope.alloc_string("registry-key")?;
  let key_b = scope.alloc_string("registry-key")?;

  let sym_a = scope.heap_mut().symbol_for(key_a)?;
  let sym_b = scope.heap_mut().symbol_for(key_b)?;
  assert_eq!(sym_a, sym_b);
  Ok(())
}

#[test]
fn symbol_for_does_not_clone_key_string_contents_on_lookup() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let sym;
  let key;
  {
    let mut scope = heap.scope();

    // Large enough that cloning the UTF-16 buffer is easily detectable, but small enough to keep
    // the test fast.
    let long = "x".repeat(16 * 1024);
    key = scope.alloc_string(&long)?;

    sym = scope.heap_mut().symbol_for(key)?;

    // Ensure `sym` is live so the registry and description remain valid even if a GC is triggered.
    scope.push_root(Value::Symbol(sym))?;
  }

  // The key lookup path should not allocate a second copy of the key's UTF-16 buffer.
  reset_allocated_bytes();
  let sym2 = heap.symbol_for(key)?;
  assert_eq!(sym, sym2);

  let allocated = allocated_bytes();
  assert!(
    allocated < 4096,
    "expected `symbol_for` lookup to allocate little-to-nothing, but it allocated {allocated} bytes"
  );

  Ok(())
}

#[test]
fn symbol_for_eventually_returns_oom_with_tight_heap_limits() -> Result<(), VmError> {
  // Keep the limit small so we reach OOM quickly, but large enough to allocate a few keys/symbols.
  let max_bytes = 1024;
  let mut heap = Heap::new(HeapLimits::new(max_bytes, max_bytes / 2));
  let mut scope = heap.scope();

  let mut saw_oom = false;
  for i in 0..10_000usize {
    let key = match scope.alloc_string(&format!("k{i}")) {
      Ok(s) => s,
      Err(VmError::OutOfMemory) => {
        saw_oom = true;
        break;
      }
      Err(e) => return Err(e),
    };

    match scope.heap_mut().symbol_for(key) {
      Ok(_) => {}
      Err(VmError::OutOfMemory) => {
        saw_oom = true;
        break;
      }
      Err(e) => return Err(e),
    }
  }

  assert!(saw_oom, "expected repeated `symbol_for` calls to eventually hit VmError::OutOfMemory");
  assert!(
    scope.heap().used_bytes() <= max_bytes,
    "heap.used_bytes should never exceed the configured max_bytes"
  );

  // `JsSymbol` should be counted in `used_bytes` so this test remains meaningful if its size
  // changes.
  assert!(
    mem::size_of::<vm_js::JsSymbol>() <= max_bytes,
    "test invariant: a single symbol should fit within the heap limit"
  );

  Ok(())
}
