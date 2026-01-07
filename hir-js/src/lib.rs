//! Deterministic lowering from `parse-js` AST into a semantic-friendly HIR.
//!
//! `hir-js` turns a `parse-js` [`parse_js::ast::stx::TopLevel`] AST into a
//! [`HirFile`] plus per-definition bodies and arenas, assigning deterministic IDs
//! (`DefId`, `BodyId`, `ExprId`, `PatId`, `TypeExprId`) and building a [`SpanMap`]
//! for byte-offset lookups.
//!
//! Call [`lower_file`] if you already have a parsed AST. For tests and simple
//! tooling, [`lower_from_source_with_kind`] parses and lowers in one step.
//!
//! # Example
//! ```
//! use hir_js::{lower_from_source_with_kind, FileKind};
//!
//! let lowered = lower_from_source_with_kind(FileKind::Ts, "export const x = 1;").unwrap();
//! assert_eq!(lowered.hir.file_kind, FileKind::Ts);
//! ```
//!
//! # Runnable example
//!
//! ```bash
//! cargo run -p hir-js --example basic_lowering
//! ```

pub mod hir;
pub mod ids;
pub mod intern;
pub mod lower;
mod lower_types;
pub mod span_map;

use diagnostics::FileId;
pub use hir::ArrayElement;
pub use hir::ArrayLiteral;
pub use hir::ArrayPat;
pub use hir::ArrayPatElement;
pub use hir::AssignOp;
pub use hir::BinaryOp;
pub use hir::Body;
pub use hir::BodyKind;
pub use hir::CallArg;
pub use hir::CallExpr;
pub use hir::ClassBody;
pub use hir::ClassMember;
pub use hir::ClassMemberAccessibility;
pub use hir::ClassMemberKey;
pub use hir::ClassMemberKind;
pub use hir::ClassMemberSig;
pub use hir::ClassMemberSigKind;
pub use hir::ClassMethodKind;
pub use hir::ConditionalType;
pub use hir::Decorator;
pub use hir::DefData;
pub use hir::DefTypeInfo;
pub use hir::EnumMemberInfo;
pub use hir::EnumMemberValue;
pub use hir::Export;
pub use hir::ExportAlias;
pub use hir::ExportAll;
pub use hir::ExportAsNamespace;
pub use hir::ExportAssignment;
pub use hir::ExportDefault;
pub use hir::ExportDefaultValue;
pub use hir::ExportKind;
pub use hir::ExportNamed;
pub use hir::ExportSpecifier;
pub use hir::Expr;
pub use hir::ExprKind;
pub use hir::FileKind;
pub use hir::ForHead;
pub use hir::ForInit;
pub use hir::FunctionBody;
pub use hir::FunctionData;
pub use hir::HirFile;
pub use hir::Import;
pub use hir::ImportBinding;
pub use hir::ImportEquals;
pub use hir::ImportEqualsTarget;
pub use hir::ImportEs;
pub use hir::ImportKind;
pub use hir::ImportNamed;
pub use hir::JsxAttr;
pub use hir::JsxAttrValue;
pub use hir::JsxChild;
pub use hir::JsxElement;
pub use hir::JsxElementName;
pub use hir::JsxExprContainer;
pub use hir::JsxMemberExpr;
pub use hir::JsxName;
pub use hir::Literal;
pub use hir::LowerResult;
pub use hir::MemberExpr;
pub use hir::ModuleAttributes;
pub use hir::ModuleSpecifier;
pub use hir::ObjectKey;
pub use hir::ObjectLiteral;
pub use hir::ObjectPat;
pub use hir::ObjectPatProp;
pub use hir::ObjectProperty;
pub use hir::Param;
pub use hir::Pat;
pub use hir::PatKind;
pub use hir::PropertyName;
pub use hir::Stmt;
pub use hir::StmtKind;
pub use hir::TemplateLiteral;
pub use hir::TemplateLiteralSpan;
pub use hir::TypeArenas;
pub use hir::TypeArenasByDef;
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
pub use hir::UnaryOp;
pub use hir::UpdateOp;
pub use hir::VarDecl;
pub use hir::VarDeclKind;
pub use hir::VarDeclarator;
pub use ids::BodyId;
pub use ids::DefId;
pub use ids::DefKind;
pub use ids::DefPath;
pub use ids::ExportId;
pub use ids::ExportSpecifierId;
pub use ids::ExprId;
pub use ids::ImportId;
pub use ids::ImportSpecifierId;
pub use ids::NameId;
pub use ids::PatId;
pub use ids::StmtId;
pub use ids::TypeExprId;
pub use ids::TypeMemberId;
pub use ids::TypeParamId;
pub use intern::NameInterner;
pub use lower::lower_file;
pub use lower::lower_file_with_diagnostics;
pub use lower::lower_file_with_diagnostics_with_cancellation;
use parse_js::parse_with_options;
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
/// [`lower_file`] if diagnostics are not needed). Source must be valid UTF-8
/// since spans and identifier handling are defined over UTF-8 byte offsets.
pub fn lower_from_source(source: &str) -> Result<LowerResult, LowerError> {
  lower_from_source_with_kind(FileKind::Ts, source)
}

pub fn lower_from_source_with_kind(
  file_kind: FileKind,
  source: &str,
) -> Result<LowerResult, LowerError> {
  let parsed = parse_with_options(
    source,
    parse_js::ParseOptions {
      dialect: match file_kind {
        FileKind::Js => parse_js::Dialect::Js,
        FileKind::Jsx => parse_js::Dialect::Jsx,
        FileKind::Ts => parse_js::Dialect::Ts,
        FileKind::Tsx => parse_js::Dialect::Tsx,
        FileKind::Dts => parse_js::Dialect::Dts,
      },
      source_type: parse_js::SourceType::Module,
    },
  )?;
  Ok(lower_file(FileId(0), file_kind, &parsed))
}

/// Fuzzing entry point to exercise parsing + lowering without panicking.
#[cfg(feature = "fuzzing")]
#[doc(hidden)]
pub fn fuzz_lower(data: &[u8]) {
  let source = String::from_utf8_lossy(data);
  let _ = lower_from_source(&source);
}
