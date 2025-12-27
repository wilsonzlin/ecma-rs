use std::sync::atomic::{AtomicUsize, Ordering};

/// Global instrumentation hook for counting actual parse executions.
static PARSE_CALLS: AtomicUsize = AtomicUsize::new(0);

/// Number of times parsing has been performed since the last reset.
///
/// This is incremented inside the salsa `parse_for` query implementation, so
/// cached reads do not affect the count—only real recomputation does. Tests can
/// rely on this to assert “no reparse” behaviour across repeated query calls.
pub fn parse_call_count() -> usize {
  PARSE_CALLS.load(Ordering::Relaxed)
}

/// Reset the parse invocation counter to zero.
pub fn reset_parse_call_count() {
  PARSE_CALLS.store(0, Ordering::Relaxed);
}

/// Record a single parse invocation.
pub(crate) fn record_parse_call() {
  PARSE_CALLS.fetch_add(1, Ordering::Relaxed);
}
