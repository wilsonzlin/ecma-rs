use crate::diagnostic::Diagnostic;
use std::error::Error;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BodyId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostError {
  MissingFileText { file: FileId },
  ResolveFailed { from: FileId, specifier: String },
}

impl fmt::Display for HostError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      HostError::MissingFileText { file } => write!(f, "missing text for file {file}"),
      HostError::ResolveFailed { from, specifier } => {
        write!(f, "failed to resolve '{specifier}' from file {from}")
      }
    }
  }
}

impl Error for HostError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ice {
  pub message: String,
  pub context: Vec<(String, String)>,
}

impl Ice {
  pub fn new(message: impl Into<String>) -> Self {
    Self {
      message: message.into(),
      context: Vec::new(),
    }
  }

  pub fn with_context(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
    self.context.push((key.into(), value.into()));
    self
  }

  pub fn to_diagnostic(&self, backtrace: Option<String>) -> Diagnostic {
    Diagnostic::ice(self, backtrace)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FatalError {
  Host(HostError),
  Cancelled,
  Ice(Ice),
}

impl From<HostError> for FatalError {
  fn from(value: HostError) -> Self {
    FatalError::Host(value)
  }
}

impl From<Ice> for FatalError {
  fn from(value: Ice) -> Self {
    FatalError::Ice(value)
  }
}

impl fmt::Display for FatalError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      FatalError::Host(err) => write!(f, "host error: {err}"),
      FatalError::Cancelled => write!(f, "checking cancelled"),
      FatalError::Ice(ice) => write!(f, "internal error: {}", ice.message),
    }
  }
}

impl Error for FatalError {}

impl fmt::Display for FileId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl fmt::Display for BodyId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}
