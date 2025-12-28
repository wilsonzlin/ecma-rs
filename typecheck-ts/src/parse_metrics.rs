use std::cell::Cell;
use std::thread_local;

/// Thread-local instrumentation hook for counting actual parse executions.
thread_local! {
  static PARSE_CALLS: Cell<usize> = const { Cell::new(0) };
}

/// Number of times parsing has been performed since the last reset.
///
/// This is incremented inside the salsa `parse_for` query implementation, so
/// cached reads do not affect the count—only real recomputation does. Tests can
/// rely on this to assert “no reparse” behaviour across repeated query calls.
pub fn parse_call_count() -> usize {
  PARSE_CALLS.with(|calls| calls.get())
}

/// Reset the parse invocation counter to zero.
pub fn reset_parse_call_count() {
  PARSE_CALLS.with(|calls| calls.set(0));
}

/// Record a single parse invocation.
pub(crate) fn record_parse_call() {
  PARSE_CALLS.with(|calls| calls.set(calls.get() + 1));
}
