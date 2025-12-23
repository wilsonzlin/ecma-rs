pub mod hir;
pub mod ids;
pub mod intern;
pub mod lower;
pub mod span_map;

pub use hir::{Body, BodyKind, DefData, Expr, ExprKind, HirFile, LowerResult, Pat, PatKind, Stmt, StmtKind};
pub use ids::{BodyId, DefId, DefKind, DefPath, ExprId, NameId, PatId, StmtId};
pub use intern::NameInterner;
pub use lower::lower_file;
pub use span_map::SpanMap;

use diagnostics::FileId;
use parse_js::parse;

#[derive(Debug, thiserror::Error)]
pub enum LowerError {
  #[error("parse error: {0}")]
  Parse(#[from] parse_js::error::SyntaxError),
}

/// Parse JS/TS source and lower it into HIR for a synthetic file id.
///
/// This is primarily a convenience for tests and fuzzing; callers that already
/// have parsed ASTs should use [`lower_file`] directly.
pub fn lower_from_source(source: &str) -> Result<LowerResult, LowerError> {
  let parsed = parse(source)?;
  Ok(lower_file(FileId(0), &parsed))
}

/// Fuzzing entry point to exercise parsing + lowering without panicking.
#[cfg(feature = "fuzzing")]
pub fn fuzz_lower(data: &[u8]) {
  let source = String::from_utf8_lossy(data);
  let _ = lower_from_source(&source);
}
