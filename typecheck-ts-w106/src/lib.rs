//! Minimal type checking stub wired to parser + HIR lowering.
//!
//! The purpose of this crate in this repository state is to provide
//! panic-resistant end-to-end wiring (parse -> lower -> check) for fuzzing and
//! property testing. Real type checking logic will replace the stubbed
//! `Checker` later; for now we ensure diagnostics are surfaced instead of
//! panics.

use hir_js_w106::lower_from_source;
use parse_js::error::SyntaxError;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CheckError {
  #[error("parse error: {0}")]
  Parse(#[from] SyntaxError),
  #[error("lowering error: {0}")]
  Lower(#[from] hir_js_w106::LowerError),
  #[error("internal error: {0}")]
  Internal(String),
}

#[derive(Debug, Default, Clone)]
pub struct Diagnostic {
  pub message: String,
}

#[derive(Debug, Default)]
pub struct CheckerResult {
  pub diagnostics: Vec<Diagnostic>,
}

/// Stub type checker: parse, lower, and emit no diagnostics unless the input
/// fails earlier phases. This function must not panic; failures are converted
/// into diagnostics.
pub fn check(source: &str) -> CheckerResult {
  let mut result = CheckerResult::default();
  match lower_from_source(source) {
    Ok(_) => {
      // No-op checker for now.
    }
    Err(err) => match err {
      hir_js_w106::LowerError::Parse(parse_err) => {
        result.diagnostics.push(Diagnostic {
          message: format!("parse error: {parse_err}"),
        });
      }
      hir_js_w106::LowerError::MissingScope { loc, context } => {
        result.diagnostics.push(Diagnostic {
          message: format!("missing scope while lowering {context} at {loc:?}"),
        });
      }
    },
  }
  result
}

/// Fuzz entry point to exercise parse -> lower -> check without panicking.
#[cfg(feature = "fuzzing")]
pub fn fuzz_check(data: &[u8]) {
  let source = String::from_utf8_lossy(data);
  let _ = check(&source);
}
