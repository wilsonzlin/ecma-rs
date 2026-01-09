//! Execution-context stack primitives.
//!
//! The ECMAScript specification models evaluation as operating on an *execution context stack*.
//! Each context records (among other things) the current Realm and the currently-running Script or
//! Module record.
//!
//! This crate does **not** implement modules yet; however, the host hooks for module loading and
//! dynamic `import()` need to observe:
//!
//! - the **current Realm** ("where should new objects/closures be created?"), and
//! - the **active script or module** (used for `import.meta`, dynamic import, etc.).
//!
//! The VM stores a stack of [`ExecutionContext`] values and exposes spec-shaped queries such as
//! [`crate::Vm::get_active_script_or_module`].

use crate::RealmId;

/// Opaque identifier for a Script Record.
///
/// This is currently a placeholder newtype so host embeddings can thread through a stable token
/// while the engine is still evaluator-independent.
///
/// In a future module/script implementation, this will be backed by real Script Records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ScriptId(u64);

impl ScriptId {
  /// Create a new `ScriptId` from an opaque numeric value.
  ///
  /// The numeric representation is intentionally unspecified; it may change.
  #[inline]
  pub const fn from_raw(raw: u64) -> Self {
    Self(raw)
  }

  /// Returns the underlying opaque numeric representation.
  #[inline]
  pub const fn to_raw(self) -> u64 {
    self.0
  }
}

/// Opaque identifier for a Module Record.
///
/// This is currently a placeholder newtype so host embeddings can thread through a stable token
/// while the engine is still evaluator-independent.
///
/// In a future module implementation, this will be backed by real Module Records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ModuleId(u64);

impl ModuleId {
  /// Create a new `ModuleId` from an opaque numeric value.
  ///
  /// The numeric representation is intentionally unspecified; it may change.
  #[inline]
  pub const fn from_raw(raw: u64) -> Self {
    Self(raw)
  }

  /// Returns the underlying opaque numeric representation.
  #[inline]
  pub const fn to_raw(self) -> u64 {
    self.0
  }
}

/// Identifies the currently-running Script or Module record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScriptOrModule {
  Script(ScriptId),
  Module(ModuleId),
}

/// A minimal spec-shaped execution context.
///
/// This corresponds to the per-entry records in ECMA-262's *execution context stack*, but is
/// intentionally scoped down to the fields required by host module integration:
///
/// - `realm` is the realm the code runs in.
/// - `script_or_module` is the active Script/Module record (if any).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExecutionContext {
  pub realm: RealmId,
  pub script_or_module: Option<ScriptOrModule>,
}

