//! Minimal HIR lowering stub that round-trips the parse tree to ensure we have
//! a deterministic, non-panicking path from tokens to a lowered form.
//!
//! Lowering expects the parse tree to be annotated with scopes via
//! [`symbol_js::compute_symbols`] if you want identifier symbols populated in
//! [`Ident`]. Calling [`lower_top_level`] without scope annotations will return
//! [`LowerError::MissingScope`] instead of silently treating identifiers as
//! globals/builtins.

pub mod lower;

pub use lower::{lower_from_source, lower_top_level, HirRoot, Ident, LowerError};

#[cfg(feature = "fuzzing")]
pub use lower::fuzz_lower;
