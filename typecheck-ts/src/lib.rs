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
//! use std::sync::Arc;
//! use typecheck_ts::{ExprId, FileKey, MemoryHost, Program};
//!
//! let mut host = MemoryHost::default();
//! let key = FileKey::new("entry.ts");
//! host.insert(
//!   key.clone(),
//!   Arc::from("export function add(a: number, b: number) { return a + b; }"),
//! );
//! let program = Program::new(host, vec![key.clone()]);
//! let diagnostics = program.check();
//! assert!(diagnostics.is_empty());
//!
//! let file_id = program.file_id(&key).unwrap();
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
//! use std::sync::Arc;
//! use typecheck_ts::{ExportMap, FileKey, MemoryHost, Program};
//!
//! let mut host = MemoryHost::default();
//! let entry = FileKey::new("entry.ts");
//! let math = FileKey::new("math.ts");
//! host.insert(
//!   entry.clone(),
//!   Arc::from("import { add } from \"./math\";\nexport const total = add(1, 2);"),
//! );
//! host.insert(
//!   math.clone(),
//!   Arc::from("export function add(a: number, b: number): number { return a + b; }"),
//! );
//! host.link(entry.clone(), "./math", math.clone());
//!
//! let program = Program::new(host, vec![entry.clone()]);
//! let diagnostics = program.check();
//! assert!(diagnostics.is_empty());
//!
//! let entry_id = program.file_id(&entry).unwrap();
//! let exports: ExportMap = program.exports_of(entry_id);
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
mod error;
mod expand;
#[cfg(feature = "fuzzing")]
mod fuzz;
mod profile;
mod program;
#[cfg(feature = "serde")]
mod snapshot;
mod type_queries;

pub use api::*;
pub use error::*;
#[cfg(feature = "fuzzing")]
pub use fuzz::*;
pub use profile::*;
pub use program::*;
#[cfg(feature = "serde")]
pub use snapshot::*;
pub use type_queries::*;

/// Generic type checking helpers (instantiation and inference).
///
/// This module intentionally re-exports internal building blocks from the main
/// checker implementation so callers can experiment with standalone inference.
pub mod check {
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

  pub mod hir_body {
    pub use crate::program::check::hir_body::*;
  }
}

pub mod queries;

/// Utilities for selecting bundled `.d.ts` libraries and compiler options.
pub mod lib_support;

/// Optional helpers for deterministic module resolution and path normalisation.
#[cfg(feature = "resolve")]
pub mod resolve;
