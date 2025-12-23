use crate::error::HostError;
use crate::error::Ice;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
  Error,
  Warning,
  Note,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
  pub code: &'static str,
  pub message: String,
  pub severity: DiagnosticSeverity,
  pub notes: Vec<String>,
  pub context: Vec<(String, String)>,
  #[cfg(feature = "capture-backtrace")]
  pub backtrace: Option<String>,
}

impl Diagnostic {
  pub fn ice(ice: &Ice, backtrace: Option<String>) -> Self {
    #[cfg(not(feature = "capture-backtrace"))]
    let _ = backtrace;

    let mut diag = Diagnostic {
      code: "ICE0001",
      message: format!("internal error: {}", ice.message),
      severity: DiagnosticSeverity::Error,
      notes: vec![],
      context: ice.context.clone(),
      #[cfg(feature = "capture-backtrace")]
      backtrace,
    };

    diag.notes.extend(
      ice
        .context
        .iter()
        .map(|(k, v)| format!("context {k} = {v}")),
    );

    diag
  }

  pub fn host(error: &HostError) -> Self {
    let (code, message, context) = match error {
      HostError::MissingFileText { file } => (
        "HOST0001",
        format!("missing text for file {file}"),
        vec![("file".into(), file.0.to_string())],
      ),
      HostError::ResolveFailed { from, specifier } => (
        "HOST0002",
        format!("failed to resolve '{specifier}' from file {from}"),
        vec![
          ("from".into(), from.0.to_string()),
          ("specifier".into(), specifier.clone()),
        ],
      ),
    };

    Diagnostic {
      code,
      message,
      severity: DiagnosticSeverity::Error,
      notes: vec![],
      context,
      #[cfg(feature = "capture-backtrace")]
      backtrace: None,
    }
  }

  pub fn cancelled() -> Self {
    Diagnostic {
      code: "CANCELLED",
      message: "checking was cancelled".to_string(),
      severity: DiagnosticSeverity::Error,
      notes: vec![],
      context: vec![],
      #[cfg(feature = "capture-backtrace")]
      backtrace: None,
    }
  }
}
