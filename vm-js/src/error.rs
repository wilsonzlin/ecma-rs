use crate::source::StackFrame;
use crate::value::Value;
use diagnostics::Diagnostic;
use std::fmt::Display;

/// Errors produced by the VM.
#[derive(Debug, Clone, thiserror::Error)]
pub enum VmError {
  /// A JavaScript `throw` value. This is catchable from JS.
  #[error("uncaught exception")]
  Throw(Value),
  /// A non-catchable termination condition (fuel exhausted, deadline exceeded,
  /// host interrupt, etc).
  #[error("{0}")]
  Termination(Termination),
  /// Early (syntax/binding) errors produced before execution begins.
  #[error("syntax error")]
  Syntax(Vec<Diagnostic>),
}

/// A non-catchable error that terminates execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Termination {
  pub reason: TerminationReason,
  pub stack: Vec<StackFrame>,
}

impl Termination {
  pub fn new(reason: TerminationReason, stack: Vec<StackFrame>) -> Self {
    Self { reason, stack }
  }
}

impl Display for Termination {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{reason}", reason = self.reason)
  }
}

/// The reason execution terminated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TerminationReason {
  OutOfFuel,
  DeadlineExceeded,
  Interrupted,
  OutOfMemory,
  StackOverflow,
}

impl Display for TerminationReason {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TerminationReason::OutOfFuel => f.write_str("execution terminated: out of fuel"),
      TerminationReason::DeadlineExceeded => f.write_str("execution terminated: deadline exceeded"),
      TerminationReason::Interrupted => f.write_str("execution terminated: interrupted"),
      TerminationReason::OutOfMemory => f.write_str("execution terminated: out of memory"),
      TerminationReason::StackOverflow => f.write_str("execution terminated: stack overflow"),
    }
  }
}

