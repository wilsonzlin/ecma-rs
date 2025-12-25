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
//! # Example: single-file function typing
//!
//! ```rust
//! use std::collections::HashMap;
//! use std::sync::Arc;
//! use typecheck_ts::{ExprId, FileId, Host, HostError, Program};
//!
//! #[derive(Default)]
//! struct MemoryHost {
//!   files: HashMap<FileId, Arc<str>>,
//! }
//!
//! impl MemoryHost {
//!   fn insert(&mut self, id: FileId, source: &str) {
//!     self.files.insert(id, Arc::from(source.to_string()));
//!   }
//! }
//!
//! impl Host for MemoryHost {
//!   fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
//!     self
//!       .files
//!       .get(&file)
//!       .cloned()
//!       .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
//!   }
//!
//!   fn resolve(&self, _from: FileId, _spec: &str) -> Option<FileId> {
//!     None
//!   }
//! }
//!
//! let mut host = MemoryHost::default();
//! host.insert(
//!   FileId(0),
//!   "export function add(a: number, b: number) { return a + b; }",
//! );
//! let program = Program::new(host, vec![FileId(0)]);
//! let diagnostics = program.check();
//! assert!(diagnostics.is_empty());
//!
//! let exports = program.exports_of(FileId(0));
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
//! use typecheck_ts::{ExportMap, FileId, Host, HostError, Program};
//!
//! #[derive(Default)]
//! struct MemoryHost {
//!   files: HashMap<FileId, Arc<str>>,
//!   edges: HashMap<(FileId, String), FileId>,
//! }
//!
//! impl MemoryHost {
//!   fn insert(&mut self, id: FileId, source: &str) {
//!     self.files.insert(id, Arc::from(source.to_string()));
//!   }
//!
//!   fn link(&mut self, from: FileId, specifier: &str, to: FileId) {
//!     self.edges.insert((from, specifier.to_string()), to);
//!   }
//! }
//!
//! impl Host for MemoryHost {
//!   fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
//!     self
//!       .files
//!       .get(&file)
//!       .cloned()
//!       .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
//!   }
//!
//!   fn resolve(&self, from: FileId, spec: &str) -> Option<FileId> {
//!     self.edges.get(&(from, spec.to_string())).copied()
//!   }
//! }
//!
//! let mut host = MemoryHost::default();
//! host.insert(
//!   FileId(0),
//!   "import { add } from \"./math\";\nexport const total = add(1, 2);",
//! );
//! host.insert(
//!   FileId(1),
//!   "export function add(a: number, b: number): number { return a + b; }",
//! );
//! host.link(FileId(0), "./math", FileId(1));
//!
//! let program = Program::new(host, vec![FileId(0)]);
//! let diagnostics = program.check();
//! assert!(diagnostics.is_empty());
//!
//! let exports: ExportMap = program.exports_of(FileId(0));
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
mod error;
mod program;

pub use api::*;
pub use error::*;
pub use program::*;

/// Generic type checking helpers (instantiation and inference).
///
/// This module intentionally re-exports internal building blocks from the main
/// checker implementation so callers can experiment with standalone inference.
pub mod check {
  pub mod infer {
    pub use crate::program::check::infer::*;
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

  pub mod class;
  pub mod relate_hooks;
}

pub mod queries;

/// Utilities for selecting bundled `.d.ts` libraries and the legacy lib checker.
///
/// The deprecated [`lib_support::LibCheckProgram`] is a string-scanning stub,
/// not the real [`Program`] type checker.
pub mod lib_support;
