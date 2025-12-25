use thiserror::Error;

use crate::{BodyId, DefId, FileId};

/// Error returned by a [`Host`](crate::Host).
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Error, Clone)]
#[error("{message}")]
pub struct HostError {
  pub(crate) message: String,
}

impl HostError {
  /// Create a new host error with the given message.
  pub fn new(message: impl Into<String>) -> HostError {
    HostError {
      message: message.into(),
    }
  }
}

/// Context associated with an internal compiler error.
#[derive(Debug, Clone, Default)]
pub struct IceContext {
  pub file: Option<FileId>,
  pub def: Option<DefId>,
  pub body: Option<BodyId>,
}

/// Internal compiler error raised when the checker encounters an invariant violation.
#[derive(Debug, Clone)]
pub struct Ice {
  pub message: String,
  pub context: IceContext,
  pub backtrace: Option<String>,
}

impl Ice {
  /// Construct a new ICE with optional context.
  pub fn new(message: impl Into<String>, context: IceContext) -> Ice {
    let backtrace = capture_backtrace();
    Ice {
      message: message.into(),
      context,
      backtrace,
    }
  }

  pub fn from_panic(payload: Box<dyn std::any::Any + Send>) -> Ice {
    let message = if let Some(msg) = payload.downcast_ref::<&str>() {
      msg.to_string()
    } else if let Some(msg) = payload.downcast_ref::<String>() {
      msg.clone()
    } else {
      "panic".to_string()
    };
    Ice::new(message, IceContext::default())
  }
}

/// Fatal, unrecoverable error during checking.
#[derive(Debug, Error)]
pub enum FatalError {
  #[error("host error: {0}")]
  Host(#[from] HostError),
  #[error("operation cancelled")]
  Cancelled,
  #[error("internal compiler error: {0:?}")]
  Ice(Ice),
  #[error("out of memory")]
  OutOfMemory,
}

fn capture_backtrace() -> Option<String> {
  if std::env::var("TYPECHECK_TS_CAPTURE_BACKTRACE").is_ok() {
    Some(format!("{:?}", std::backtrace::Backtrace::force_capture()))
  } else {
    None
  }
}
