pub mod hir;
pub mod ids;
pub mod intern;
pub mod lower;
mod lower_types;
pub mod span_map;

use diagnostics::FileId;
pub use hir::Body;
pub use hir::BodyKind;
pub use hir::ConditionalType;
pub use hir::DefData;
pub use hir::DefTypeInfo;
pub use hir::Expr;
pub use hir::ExprKind;
pub use hir::HirFile;
pub use hir::LowerResult;
pub use hir::Pat;
pub use hir::PatKind;
pub use hir::PropertyName;
pub use hir::Stmt;
pub use hir::StmtKind;
pub use hir::TypeArenas;
pub use hir::TypeExpr;
pub use hir::TypeExprKind;
pub use hir::TypeFnParam;
pub use hir::TypeFunction;
pub use hir::TypeImport;
pub use hir::TypeIndexSignature;
pub use hir::TypeLiteral;
pub use hir::TypeLiteralType;
pub use hir::TypeMapped;
pub use hir::TypeMappedModifier;
pub use hir::TypeMember;
pub use hir::TypeMemberKind;
pub use hir::TypeMethodSignature;
pub use hir::TypeName;
pub use hir::TypeParam;
pub use hir::TypePredicate;
pub use hir::TypePropertySignature;
pub use hir::TypeRef;
pub use hir::TypeSignature;
pub use hir::TypeTemplateLiteral;
pub use hir::TypeTemplateLiteralSpan;
pub use hir::TypeTuple;
pub use hir::TypeTupleElement;
pub use hir::TypeVariance;
pub use ids::BodyId;
pub use ids::DefId;
pub use ids::DefKind;
pub use ids::DefPath;
pub use ids::ExprId;
pub use ids::NameId;
pub use ids::PatId;
pub use ids::StmtId;
pub use ids::TypeExprId;
pub use ids::TypeMemberId;
pub use ids::TypeParamId;
pub use intern::NameInterner;
pub use lower::lower_file;
pub use lower::lower_file_with_diagnostics;
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
/// have parsed ASTs should prefer [`lower_file_with_diagnostics`] (or
/// [`lower_file`] if diagnostics are not needed).
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
