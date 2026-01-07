use std::cell::Cell;
use std::thread_local;

thread_local! {
  /// Thread-local instrumentation hook for counting actual declaration type
  /// query executions.
  static DECL_TYPES_CALLS: Cell<usize> = const { Cell::new(0) };
}

/// Number of times the `decl_types` salsa query has been recomputed since the
/// last reset.
///
/// This counter is incremented inside the salsa `decl_types_for` query
/// implementation, so cached reads do not affect the count—only real
/// recomputation does. Tests can rely on this to assert that edits only trigger
/// per-file declaration work when expected.
pub fn decl_types_call_count() -> usize {
  DECL_TYPES_CALLS.with(|calls| calls.get())
}

/// Reset the decl-types invocation counter to zero.
pub fn reset_decl_types_call_count() {
  DECL_TYPES_CALLS.with(|calls| calls.set(0));
}

/// Record a single decl-types query execution.
pub(crate) fn record_decl_types_call() {
  DECL_TYPES_CALLS.with(|calls| calls.set(calls.get() + 1));
}
