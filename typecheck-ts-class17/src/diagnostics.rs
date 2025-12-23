/// Diagnostic codes for the lightweight checker.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DiagnosticCode {
  ImplementsIncompatible,
  ExtendsIncompatible,
  PrivateIncompatible,
  ProtectedIncompatible,
  PropertyNotDefinitelyAssigned,
  InvalidMemberAccess,
}

/// Minimal diagnostic structure capturing the code and a human readable message.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagnostic {
  pub code: DiagnosticCode,
  pub message: String,
}

impl Diagnostic {
  pub fn new(code: DiagnosticCode, message: impl Into<String>) -> Self {
    Self {
      code,
      message: message.into(),
    }
  }
}
