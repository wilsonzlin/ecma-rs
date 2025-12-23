use serde::Deserialize;
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Span {
  pub file: u32,
  pub start: u32,
  pub end: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Severity {
  Error,
  Warning,
  Note,
}

impl Default for Severity {
  fn default() -> Self {
    Severity::Error
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
  pub code: String,
  pub message: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub span: Option<Span>,
  #[serde(default)]
  pub severity: Severity,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub notes: Vec<String>,
}

impl Diagnostic {
  pub fn new(code: impl Into<String>, message: impl Into<String>, span: Option<Span>) -> Self {
    Self {
      code: code.into(),
      message: message.into(),
      span,
      severity: Severity::Error,
      notes: Vec::new(),
    }
  }
}
