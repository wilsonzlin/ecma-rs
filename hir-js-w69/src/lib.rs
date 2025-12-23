//! Minimal high-level IR for JavaScript lowering.
//!
//! This crate provides a compact, optimizer-friendly HIR with stable IDs and
//! source locations. It mirrors the subset of JavaScript currently consumed by
//! the optimizer and exposes a lowering entry point from the `parse-js` AST.
//!
//! ```rust
//! use hir_js_w69::lower_top_level;
//! use symbol_js::{compute_symbols, TopLevelMode};
//!
//! let source = "const x = (y) => y + 1;";
//! let mut parsed = parse_js::parse(source).unwrap();
//! compute_symbols(&mut parsed, TopLevelMode::Module);
//! let hir = lower_top_level(&parsed).unwrap();
//! assert_eq!(hir.bodies.len(), 2); // top-level + arrow function
//! ```

mod hir;
mod ids;
mod lower;

pub use hir::*;
pub use ids::*;
pub use lower::*;
