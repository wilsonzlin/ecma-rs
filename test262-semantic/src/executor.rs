use crate::runner::TestCase;
use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecPhase {
  Parse,
  Resolution,
  Runtime,
}

impl ExecPhase {
  pub fn as_str(self) -> &'static str {
    match self {
      ExecPhase::Parse => "parse",
      ExecPhase::Resolution => "resolution",
      ExecPhase::Runtime => "runtime",
    }
  }
}

impl fmt::Display for ExecPhase {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.as_str())
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsError {
  pub phase: ExecPhase,
  /// The JavaScript error "type" name when known (e.g. `SyntaxError`, `TypeError`).
  pub typ: Option<String>,
  pub message: String,
  pub stack: Option<String>,
}

impl JsError {
  pub fn new(phase: ExecPhase, typ: Option<String>, message: impl Into<String>) -> Self {
    Self {
      phase,
      typ,
      message: message.into(),
      stack: None,
    }
  }

  pub fn with_stack(mut self, stack: impl Into<String>) -> Self {
    self.stack = Some(stack.into());
    self
  }

  pub fn to_report_string(&self) -> String {
    match &self.stack {
      Some(stack) if !stack.is_empty() => format!("{}\n\n{}", self.message, stack),
      _ => self.message.clone(),
    }
  }
}

#[derive(Debug, Clone)]
pub enum ExecError {
  Js(JsError),
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
    return Box::new(crate::vm_js_executor::VmJsExecutor::default());
  }
}
