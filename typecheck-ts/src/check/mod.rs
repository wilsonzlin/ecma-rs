//! Internal helpers for checking assignments, object literals, and generic instantiation.

pub(super) mod assign;
pub(super) mod cfg;
pub(crate) mod decls;
pub(crate) mod expr;
pub(super) mod flow;
pub mod hir_body;
pub(crate) mod infer;
pub(crate) mod instantiate;
pub(super) mod modules;
pub(super) mod narrow;
pub(super) mod object_literal;
pub(crate) mod overload;
pub(crate) mod type_expr;
pub mod caches;
