//! Minimal HIR lowering stub that round-trips the parse tree to ensure we have
//! a deterministic, non-panicking path from tokens to a lowered form.
//!
//! This is intentionally small: full HIR support lives elsewhere. Here we keep
//! a placeholder `HirRoot` structure and guard it with property tests and fuzz
//! entry points to ensure termination and stability while the real lowering
//! pipeline evolves.

use parse_js::error::SyntaxError;
use parse_js::parse;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirRoot {
  /// Placeholder: number of top-level statements parsed.
  pub stmt_count: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum LowerError {
  #[error("parse error: {0}")]
  Parse(#[from] SyntaxError),
}

/// Parse JS/TS source and produce a placeholder HIR root. The emphasis is on
/// non-panicking behavior; syntax errors are surfaced as `Err`.
pub fn lower_from_source(source: &str) -> Result<HirRoot, LowerError> {
  let parsed = parse(source)?;
  Ok(HirRoot {
    stmt_count: parsed.stx.body.len(),
  })
}

/// Fuzzing entry point to exercise parsing + lowering without panicking.
#[cfg(feature = "fuzzing")]
pub fn fuzz_lower(data: &[u8]) {
  let source = String::from_utf8_lossy(data);
  let _ = lower_from_source(&source);
}
