use std::cell::Cell;
use std::thread_local;

/// Thread-local instrumentation hook for counting actual HIR lowering executions.
thread_local! {
  static LOWER_CALLS: Cell<usize> = const { Cell::new(0) };
}

/// Number of times HIR lowering has been performed since the last reset.
///
/// This is incremented inside the salsa `lower_hir_for` query implementation, so
/// cached reads do not affect the count—only real recomputation does. Tests can
/// rely on this to assert “no re-lower” behaviour across repeated query calls.
pub fn lower_call_count() -> usize {
  LOWER_CALLS.with(|calls| calls.get())
}

/// Reset the lowering invocation counter to zero.
pub fn reset_lower_call_count() {
  LOWER_CALLS.with(|calls| calls.set(0));
}

/// Record a single lowering invocation.
pub(crate) fn record_lower_call() {
  LOWER_CALLS.with(|calls| calls.set(calls.get() + 1));
}
