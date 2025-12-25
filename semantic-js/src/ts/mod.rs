//! TypeScript mode semantics: bind module-level declarations, imports, and
//! exports into deterministic symbol groups.
//!
//! TS mode is namespaced under `ts` to avoid collisions with JS-only scopes
//! and symbols. APIs here are still evolving.
//!
//! The binder operates over pre-lowered [`HirFile`] inputs (typically produced
//! by a frontend such as `hir-js`). [`bind_ts_program`] walks the reachable
//! files, allocates stable [`SymbolId`]s and [`DeclId`]s, and computes export
//! maps per module. It does not descend into expression bodies; the result is a
//! module graph plus merged declaration sets suitable for a future type checker
//! or downstream tooling that needs TypeScript-aware name resolution.
//!
//! See [`SymbolTable`] and related types for the in-memory representation and
//! determinism constraints.
mod binder;
pub mod from_hir_js;
pub mod locals;
mod model;

pub use binder::bind_ts_program;
pub use model::*;

#[cfg(test)]
mod tests;
