use super::*;

impl Program {
  /// Request cancellation of ongoing work.
  pub fn cancel(&self) {
    self.cancelled.store(true, Ordering::Relaxed);
  }

  /// Clear any pending cancellation request so new work can proceed.
  pub fn clear_cancellation(&self) {
    self.cancelled.store(false, Ordering::Relaxed);
  }
}
