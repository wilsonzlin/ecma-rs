use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;

/// A token observed by the VM to detect host interrupts.
#[derive(Debug, Clone)]
pub struct InterruptToken {
  interrupted: Arc<AtomicBool>,
}

impl InterruptToken {
  /// Create a new interrupt token + handle pair.
  pub fn new() -> (Self, InterruptHandle) {
    let interrupted = Arc::new(AtomicBool::new(false));
    (
      Self {
        interrupted: interrupted.clone(),
      },
      InterruptHandle { interrupted },
    )
  }

  /// Create an interrupt token + handle pair that shares an externally-owned flag.
  ///
  /// This is useful for integrating with cancellation/timeout infrastructure that already uses an
  /// `Arc<AtomicBool>` token, allowing the VM to observe the same flag without additional polling
  /// glue.
  pub fn from_shared_flag(interrupted: Arc<AtomicBool>) -> (Self, InterruptHandle) {
    (
      Self {
        interrupted: interrupted.clone(),
      },
      InterruptHandle { interrupted },
    )
  }

  pub fn is_interrupted(&self) -> bool {
    self.interrupted.load(Ordering::Relaxed)
  }
}

/// A host handle used to request that the VM terminates execution.
#[derive(Debug, Clone)]
pub struct InterruptHandle {
  interrupted: Arc<AtomicBool>,
}

impl InterruptHandle {
  /// Request that the VM cooperatively terminates at the next `Vm::tick()`.
  pub fn interrupt(&self) {
    self.interrupted.store(true, Ordering::Relaxed);
  }
}
