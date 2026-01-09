use crate::source::StackFrame;
use crate::value::Value;
use diagnostics::Diagnostic;
use std::fmt::Display;

/// Errors produced by the VM and runtime.
#[derive(Debug, Clone, thiserror::Error)]
pub enum VmError {
  /// The heap has exceeded its configured memory limit.
  #[error("out of memory")]
  OutOfMemory,

  /// A GC handle was used after the underlying allocation was freed (or the handle is otherwise
  /// malformed).
  #[error("invalid handle")]
  InvalidHandle,

  /// An attempted prototype mutation would introduce a cycle in the `[[Prototype]]` chain.
  #[error("prototype cycle")]
  PrototypeCycle,

  /// A prototype chain traversal exceeded a hard upper bound.
  #[error("prototype chain too deep")]
  PrototypeChainTooDeep,

  /// A stubbed/unfinished codepath.
  #[error("unimplemented: {0}")]
  Unimplemented(&'static str),

  /// The provided property descriptor patch is invalid.
  #[error("invalid property descriptor patch: cannot mix data and accessor fields")]
  InvalidPropertyDescriptorPatch,

  /// Object property lookup failed.
  #[error("property not found")]
  PropertyNotFound,

  /// An operation expected a data property, but an accessor property was encountered instead.
  #[error("property is not a data property")]
  PropertyNotData,

  #[error("type error: {0}")]
  TypeError(&'static str),

  /// Attempted to call a non-callable value.
  #[error("value is not callable")]
  NotCallable,

  /// Attempted to construct a non-constructable value.
  #[error("value is not a constructor")]
  NotConstructable,

  /// A JavaScript `throw` value. This is catchable from JS.
  #[error("uncaught exception")]
  Throw(Value),

  /// A non-catchable termination condition (fuel exhausted, deadline exceeded, host interrupt,
  /// etc).
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
