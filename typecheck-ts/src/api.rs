//! Public API surface for `typecheck-ts`.
//!
//! This module centralizes the small set of stable identifiers and types that
//! callers should rely on when interacting with the checker. All IDs are cheap
//! `Copy` newtypes that remain stable within the lifetime of a [`Program`].

/// Stable file identifier shared across the toolchain.
pub use diagnostics::FileId;
/// Canonical diagnostic model used throughout parsing, binding, and checking.
pub use diagnostics::{Diagnostic, Label, Severity, Span, TextRange};
/// Stable identifiers produced by lowering to HIR.
pub use hir_js::{BodyId, DefId, ExprId, PatId};
