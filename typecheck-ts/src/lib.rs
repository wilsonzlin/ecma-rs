//! TypeScript type checking facade for the ecma-rs toolchain.
//!
//! The checker exposes a small, ergonomic API centred around [`Program`] and a
//! handful of stable identifiers (`FileId`, `DefId`, `BodyId`, `ExprId`,
//! `TypeId`). A `Program` ties together a user-provided [`Host`] (for file
//! contents and module resolution), parses all reachable files, binds top-level
//! symbols, and type-checks bodies on demand. Global work is performed once per
//! file, while [`Program::check_body`] produces per-body side tables that can be
//! queried without leaking internal arenas or caches.
//!
//! All source text is treated as UTF-8. Hosts should validate/convert any raw
//! byte inputs before returning them as `Arc<str>` from [`Host::file_text`].
//!
//! # Example: single-file function typing
//!
//! ```rust
//! use std::collections::HashMap;
//! use std::sync::Arc;
//! use typecheck_ts::{ExprId, FileKey, Host, HostError, Program};
//!
//! #[derive(Default)]
//! struct MemoryHost {
//!   files: HashMap<FileKey, Arc<str>>,
//! }
//!
//! impl MemoryHost {
//!   fn insert(&mut self, key: FileKey, source: &str) {
//!     self.files.insert(key, Arc::from(source.to_string()));
//!   }
//! }
//!
//! impl Host for MemoryHost {
//!   fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
//!     self
//!       .files
//!       .get(&file)
//!       .cloned()
//!       .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
//!   }
//!
//!   fn resolve(&self, _from: &FileKey, _spec: &str) -> Option<FileKey> {
//!     None
//!   }
//! }
//!
//! let mut host = MemoryHost::default();
//! let file = FileKey::new("file0.ts");
//! host.insert(
//!   file.clone(),
//!   "export function add(a: number, b: number) { return a + b; }",
//! );
//! let program = Program::new(host, vec![file.clone()]);
//! let diagnostics = program.check();
//! assert!(diagnostics.is_empty());
//!
//! let file_id = program.file_id(&file).unwrap();
//! let exports = program.exports_of(file_id);
//! let add_def = exports.get("add").and_then(|e| e.def).unwrap();
//! let add_body = program.body_of_def(add_def).unwrap();
//! let result = program.check_body(add_body);
//! let ty = program.type_of_expr(add_body, ExprId(0));
//! assert!(result.diagnostics().is_empty());
//! assert_eq!(program.display_type(ty).to_string(), "number");
//! ```
//!
//! # Example: cross-file exports and imports
//!
//! ```rust
//! use std::collections::HashMap;
//! use std::sync::Arc;
//! use typecheck_ts::{ExportMap, FileKey, Host, HostError, Program};
//!
//! #[derive(Default)]
//! struct MemoryHost {
//!   files: HashMap<FileKey, Arc<str>>,
//!   edges: HashMap<(FileKey, String), FileKey>,
//! }
//!
//! impl MemoryHost {
//!   fn insert(&mut self, key: FileKey, source: &str) {
//!     self.files.insert(key, Arc::from(source.to_string()));
//!   }
//!
//!   fn link(&mut self, from: FileKey, specifier: &str, to: FileKey) {
//!     self.edges.insert((from, specifier.to_string()), to);
//!   }
//! }
//!
//! impl Host for MemoryHost {
//!   fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
//!     self
//!       .files
//!       .get(file)
//!       .cloned()
//!       .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
//!   }
//!
//!   fn resolve(&self, from: &FileKey, spec: &str) -> Option<FileKey> {
//!     self.edges.get(&(from.clone(), spec.to_string())).cloned()
//!   }
//! }
//!
//! let mut host = MemoryHost::default();
//! host.insert(
//!   FileKey::new("index.ts"),
//!   "import { add } from \"./math\";\nexport const total = add(1, 2);",
//! );
//! host.insert(
//!   FileKey::new("math.ts"),
//!   "export function add(a: number, b: number): number { return a + b; }",
//! );
//! host.link(FileKey::new("index.ts"), "./math", FileKey::new("math.ts"));
//!
//! let program = Program::new(host, vec![FileKey::new("index.ts")]);
//! let diagnostics = program.check();
//! assert!(diagnostics.is_empty());
//!
//! let exports = program
//!   .exports_of(program.file_id(&FileKey::new("index.ts")).unwrap());
//! let total_def = exports.get("total").unwrap().def.unwrap();
//! let total_type = program.type_of_def(total_def);
//! assert_eq!(program.display_type(total_type).to_string(), "number");
//! ```
//!
//! # Features
//!
//! - `serde` (default): enables serialization for identifiers, diagnostics, and
//!   [`TypeDisplay`] (which renders to a string for JSON outputs).
//!
//! The public API intentionally hides internal storage (arenas, caches, ASTs).
//! [`Program`] returns opaque IDs and `Arc` handles so downstream consumers can
//! cache and share results without relying on implementation details.

mod api;
pub mod codes;
#[doc(hidden)]
pub mod db;
mod error;
mod expand;
mod files;
mod parse_metrics;
mod profile;
mod program;
mod sem_hir;
#[cfg(feature = "serde")]
mod snapshot;
mod symbols;
mod type_queries;

pub use api::*;
pub use error::*;
pub use parse_metrics::{parse_call_count, reset_parse_call_count};
pub use profile::*;
pub use program::BodyCheckResult;
pub use program::*;
#[cfg(feature = "serde")]
pub use snapshot::*;
pub use symbols::*;
pub use type_queries::*;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Simple in-memory host used by tests and examples.
#[derive(Clone, Default)]
pub struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
  edges: HashMap<(FileKey, String), FileKey>,
  options: lib_support::CompilerOptions,
  libs: Vec<lib_support::LibFile>,
}

impl MemoryHost {
  /// Create a host with default compiler options.
  pub fn new() -> Self {
    Self::default()
  }

  /// Set explicit compiler options for this host.
  pub fn with_options(options: lib_support::CompilerOptions) -> Self {
    MemoryHost {
      options,
      ..Default::default()
    }
  }

  /// Insert a file keyed by [`FileKey`].
  pub fn insert(&mut self, key: FileKey, source: impl Into<Arc<str>>) {
    self.files.insert(key, source.into());
  }

  /// Link a module specifier from one file to another.
  pub fn link(&mut self, from: FileKey, specifier: &str, to: FileKey) {
    self.edges.insert((from, specifier.to_string()), to);
  }

  /// Add a library file that will be returned from [`Host::lib_files`].
  pub fn add_lib(&mut self, lib: lib_support::LibFile) {
    self.libs.push(lib);
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    if let Some(mapped) = self
      .edges
      .get(&(from.clone(), specifier.to_string()))
      .cloned()
    {
      return Some(mapped);
    }

    let from_path = Path::new(from.as_str());
    let mut resolved = PathBuf::new();
    if let Some(parent) = from_path.parent() {
      resolved.push(parent);
    }
    resolved.push(specifier);
    if resolved.extension().is_none() {
      resolved.set_extension("ts");
    }
    let mut candidate = resolved.to_string_lossy().to_string();
    if let Some(stripped) = candidate.strip_prefix("./") {
      candidate = stripped.to_string();
    }
    let normalized = diagnostics::paths::normalize_ts_path(&candidate);
    self
      .files
      .keys()
      .find(|key| key.as_str() == candidate || key.as_str() == normalized)
      .cloned()
  }

  fn compiler_options(&self) -> lib_support::CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<lib_support::LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: &FileKey) -> lib_support::FileKind {
    if self.libs.iter().any(|lib| &lib.key == file) {
      lib_support::FileKind::Dts
    } else {
      lib_support::FileKind::Ts
    }
  }
}

/// Generic type checking helpers (instantiation and inference).
///
/// This module intentionally re-exports internal building blocks from the main
/// checker implementation so callers can experiment with standalone inference.
pub mod check {
  pub mod decls {
    pub use crate::program::check::decls::*;
  }

  pub mod cfg {
    pub use crate::program::check::cfg::*;
  }

  pub mod infer {
    pub use crate::program::check::infer::*;
  }

  pub mod caches {
    pub use crate::program::check::caches::*;
  }

  pub mod instantiate {
    pub use crate::program::check::instantiate::*;
  }

  pub mod type_expr {
    pub use crate::program::check::type_expr::*;
  }

  pub mod overload {
    pub use crate::program::check::overload::*;
  }

  pub mod expr {
    pub use crate::program::check::expr::*;
  }

  pub mod flow_bindings {
    pub use crate::program::check::flow_bindings::*;
  }

  pub mod hir_body {
    pub use crate::program::check::hir_body::*;
  }

  pub mod widen {
    pub use crate::program::check::widen::*;
  }
}

pub mod queries;

/// Utilities for selecting bundled `.d.ts` libraries and compiler options.
pub mod lib_support;
