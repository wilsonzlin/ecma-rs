use crate::runner::TestCase;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub enum ExecError {
  Error(String),
  Cancelled,
  Skipped(String),
}

pub type ExecResult = std::result::Result<(), ExecError>;

pub trait Executor: Send + Sync {
  fn execute(&self, case: &TestCase, source: &str, cancel: &Arc<AtomicBool>) -> ExecResult;
}

#[cfg(feature = "stub_executor")]
#[derive(Debug, Clone, Copy, Default)]
pub struct StubExecutor;

#[cfg(feature = "stub_executor")]
impl Executor for StubExecutor {
  fn execute(&self, _case: &TestCase, _source: &str, cancel: &Arc<AtomicBool>) -> ExecResult {
    if cancel.load(std::sync::atomic::Ordering::Relaxed) {
      return Err(ExecError::Cancelled);
    }
    Ok(())
  }
}

pub fn default_executor() -> Box<dyn Executor> {
  #[cfg(feature = "stub_executor")]
  {
    return Box::new(StubExecutor);
  }

  #[cfg(not(feature = "stub_executor"))]
  {
    compile_error!(
      "test262-semantic has no default executor. Enable `--features stub_executor` or add a real JS VM executor."
    );
  }
}

