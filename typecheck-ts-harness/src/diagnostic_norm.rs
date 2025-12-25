use crate::tsc::TscDiagnostic;
use serde::{Deserialize, Serialize};
use typecheck_ts::{Diagnostic, FileId, Severity};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticEngine {
  Rust,
  Tsc,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(untagged)]
pub enum DiagnosticCode {
  Rust(String),
  Tsc(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NormalizedDiagnostic {
  pub engine: DiagnosticEngine,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub code: Option<DiagnosticCode>,
  pub file: Option<String>,
  pub start: u32,
  pub end: u32,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub severity: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub message: Option<String>,
}

pub fn normalize_rust_diagnostics(
  diags: &[Diagnostic],
  file_name: impl Fn(FileId) -> Option<String>,
) -> Vec<NormalizedDiagnostic> {
  diags
    .iter()
    .map(|diag| {
      let file = file_name(diag.primary.file);
      let start = diag.primary.range.start;
      let end = diag.primary.range.end;

      NormalizedDiagnostic {
        engine: DiagnosticEngine::Rust,
        code: Some(DiagnosticCode::Rust(diag.code.as_str().to_string())),
        file,
        start,
        end,
        severity: Some(match diag.severity {
          Severity::Error => "error".to_string(),
          Severity::Warning => "warning".to_string(),
          Severity::Note => "note".to_string(),
          Severity::Help => "help".to_string(),
        }),
        message: Some(diag.message.clone()),
      }
    })
    .collect()
}

pub fn normalize_tsc_diagnostics(diags: &[TscDiagnostic]) -> Vec<NormalizedDiagnostic> {
  diags
    .iter()
    .map(|diag| NormalizedDiagnostic {
      engine: DiagnosticEngine::Tsc,
      code: Some(DiagnosticCode::Tsc(diag.code)),
      file: diag.file.clone(),
      start: diag.start,
      end: diag.end,
      severity: diag.category.clone(),
      message: None,
    })
    .collect()
}

pub fn sort_diagnostics(diags: &mut Vec<NormalizedDiagnostic>) {
  diags.sort_by(|a, b| {
    (
      a.file.as_deref().unwrap_or(""),
      a.start,
      a.end,
      code_key(&a.code),
    )
      .cmp(&(
        b.file.as_deref().unwrap_or(""),
        b.start,
        b.end,
        code_key(&b.code),
      ))
  });
}

pub fn describe(diag: &NormalizedDiagnostic) -> String {
  let location = diag
    .file
    .as_deref()
    .map(|f| format!("{f}:{}-{}", diag.start, diag.end))
    .unwrap_or_else(|| format!("<unknown>:{}-{}", diag.start, diag.end));
  let code = diag
    .code
    .as_ref()
    .map(code_to_string)
    .unwrap_or_else(|| "unknown".to_string());
  format!("{location} [{code}]")
}

pub fn within_tolerance(a: u32, b: u32, tolerance: u32) -> bool {
  let (min, max) = if a <= b { (a, b) } else { (b, a) };
  max - min <= tolerance
}

fn code_key(code: &Option<DiagnosticCode>) -> (u8, String) {
  match code {
    Some(DiagnosticCode::Rust(val)) => (0, val.clone()),
    Some(DiagnosticCode::Tsc(val)) => (1, val.to_string()),
    None => (2, String::new()),
  }
}

fn code_to_string(code: &DiagnosticCode) -> String {
  match code {
    DiagnosticCode::Rust(c) => c.clone(),
    DiagnosticCode::Tsc(c) => c.to_string(),
  }
}
