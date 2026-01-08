use std::{error::Error, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WebIdlLimit {
  MaxStringCodeUnits,
  MaxSequenceLength,
  MaxRecordEntries,
}

/// Errors that can occur during WebIDL conversions.
#[derive(Debug)]
pub enum WebIdlError {
  JsRuntime(Box<dyn Error + Send + Sync + 'static>),
  LimitExceeded {
    limit: WebIdlLimit,
    got: usize,
    max: usize,
  },
}

impl WebIdlError {
  pub fn js<E: Error + Send + Sync + 'static>(e: E) -> Self {
    Self::JsRuntime(Box::new(e))
  }

  pub(crate) fn limit_exceeded(limit: WebIdlLimit, got: usize, max: usize) -> Self {
    Self::LimitExceeded { limit, got, max }
  }
}

impl fmt::Display for WebIdlError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      WebIdlError::JsRuntime(e) => write!(f, "js runtime error: {e}"),
      WebIdlError::LimitExceeded { limit, got, max } => {
        write!(f, "webidl limit exceeded ({limit:?}): got {got}, max {max}")
      }
    }
  }
}

impl Error for WebIdlError {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    match self {
      WebIdlError::JsRuntime(e) => Some(&**e),
      WebIdlError::LimitExceeded { .. } => None,
    }
  }
}
