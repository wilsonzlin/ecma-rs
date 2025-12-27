use std::sync::atomic::{AtomicUsize, Ordering};

/// Global instrumentation hook for counting actual parse executions.
static PARSE_CALLS: AtomicUsize = AtomicUsize::new(0);

/// Number of times parsing has been performed since the last reset.
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
