//! Public API surface for `typecheck-ts`.
//!
//! This module centralizes the small set of stable identifiers and types that
//! callers should rely on when interacting with the checker. All IDs are cheap
//! `Copy` newtypes that remain stable within the lifetime of a [`Program`].
//! Spans use UTF-8 byte offsets and are returned by helpers such as
//! [`Program::span_of_def`](crate::Program::span_of_def) and
//! [`Program::span_of_expr`](crate::Program::span_of_expr) to map identifiers
//! back to source text. Offset-based queries like
//! [`Program::symbol_at`](crate::Program::symbol_at) and
//! [`Program::type_at`](crate::Program::type_at) select the innermost symbol or
//! expression covering a position for IDE-like interactions using deterministic
//! span indexes backed by the shared `hir-js` [`SpanMap`](hir_js::span_map::SpanMap)
//! for `O(log n)` lookups instead of per-expression scans. Per-body results
//! ([`BodyCheckResult`](crate::BodyCheckResult)) expose the same indexed span
//! accessors to avoid linear walks when resolving offsets within a single body.

use std::fmt;
use std::sync::Arc;

/// Stable file identifier shared across the toolchain.
pub use diagnostics::FileId;
/// Canonical diagnostic model used throughout parsing, binding, and checking.
pub use diagnostics::{Diagnostic, Label, Severity, Span, TextRange};
/// Primary type identifier used throughout the checker.
pub use types_ts_interned::TypeId;
/// Interned `types-ts-interned` identifier for callers that need to construct or
/// inspect standalone types without the legacy `Program` API.
pub use types_ts_interned::TypeId as InternedTypeId;
/// Interned type parameter identifier used by the `TypeQueries` APIs.
pub use types_ts_interned::TypeParamId;

/// Stable identifiers produced by lowering to HIR.
pub use hir_js::{BodyId, DefId, ExprId, PatId};

/// Stable key chosen by the host to identify a file.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileKey(pub Arc<str>);

impl FileKey {
  /// Create a new key from any owned or borrowed string.
  pub fn new(key: impl Into<Arc<str>>) -> Self {
    FileKey(key.into())
  }

  /// Borrow the underlying string.
  pub fn as_str(&self) -> &str {
    &self.0
  }
}

impl fmt::Debug for FileKey {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("FileKey").field(&self.0).finish()
  }
}

impl fmt::Display for FileKey {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.as_str())
  }
}

#[cfg(feature = "serde")]
impl serde::Serialize for FileKey {
  fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(self.as_str())
  }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for FileKey {
  fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
    let s = String::deserialize(deserializer)?;
    Ok(FileKey::new(s))
  }
}

impl<T: Into<Arc<str>>> From<T> for FileKey {
  fn from(value: T) -> Self {
    FileKey::new(value)
  }
}
