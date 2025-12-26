//! Public API surface for `typecheck-ts`.
//!
//! This module centralizes the small set of stable identifiers and types that
//! callers should rely on when interacting with the checker. All IDs are cheap
//! `Copy` newtypes that remain stable within the lifetime of a [`Program`].

/// Stable file identifier shared across the toolchain.
pub use diagnostics::FileId;
/// Canonical diagnostic model used throughout parsing, binding, and checking.
pub use diagnostics::{Diagnostic, Label, Severity, Span, TextRange};
/// Interned `types-ts-interned` identifier for callers that need to construct or
/// inspect standalone types without the legacy `Program` API.
pub use types_ts_interned::TypeId as InternedTypeId;
/// Interned type parameter identifier used by the `TypeQueries` APIs.
pub use types_ts_interned::TypeParamId;

/// Stable identifiers produced by lowering to HIR.
pub use hir_js::{BodyId, DefId, ExprId, PatId};
