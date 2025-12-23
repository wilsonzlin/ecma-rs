pub mod hir;
pub mod ids;
pub mod intern;
pub mod lower;
pub mod span_map;

use diagnostics::FileId;
pub use hir::Body;
pub use hir::BodyKind;
pub use hir::DefData;
pub use hir::Expr;
pub use hir::ExprKind;
pub use hir::HirFile;
pub use hir::LowerResult;
pub use hir::Pat;
pub use hir::PatKind;
pub use hir::Stmt;
pub use hir::StmtKind;
pub use ids::BodyId;
pub use ids::DefId;
pub use ids::DefKind;
pub use ids::DefPath;
pub use ids::ExprId;
pub use ids::NameId;
pub use ids::PatId;
pub use ids::StmtId;
pub use intern::NameInterner;
pub use lower::lower_file;
use parse_js::parse;
pub use span_map::SpanMap;

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
