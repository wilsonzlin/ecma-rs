//! Unified JavaScript/TypeScript semantics shared across the workspace.
//!
//! The public API is split by language mode to keep JS-only identifiers from
//! colliding with TypeScript counterparts:
//! - [`js`]: JS-only scopes and symbols used by optimizers/minifiers.
//! - [`ts`]: TypeScript binder and model (work in progress).
//! - [`assoc`]: Helpers for reading IDs attached to `parse-js` AST nodes.
//!
//! `semantic-js` intentionally hosts two distinct entry points that share the
//! same determinism and lock-free goals:
//!
//! - [`js`] builds a lexical scope tree for JavaScript/TS syntax and attaches
//!   small identifiers to [`parse_js::ast::node::NodeAssocData`] so downstream
//!   crates such as optimizers or minifiers can query scope information without
//!   owning the AST.
//! - [`ts`] binds module-level TypeScript declarations from lowered
//!   [`ts::HirFile`] inputs, producing deterministic symbol groups and export
//!   maps for consumption by a type checker or any consumer that needs
//!   TypeScript-aware module graphs.
//!
//! Both modes avoid global locks and allocate stable identifiers sequentially
//! into vectors. Consumers should treat the IDs as opaque handles that are
//! repeatable for the same inputs; there is no support yet for cross-run
//! stability guarantees beyond deterministic traversal of the provided HIR/AST.
//!
//! ## Determinism and integration notes
//!
//! - JS mode writes attachments into [`parse_js::ast::node::NodeAssocData`];
//!   scope symbol iteration is deterministic via [`js::ScopeData::iter_symbols_sorted`]
//!   or [`js::JsSemantics::scope_symbols`].
//! - TS mode exposes only ordered structures (`BTreeMap`, sorted declaration
//!   lists) in its public API; root ordering and resolver results still drive
//!   the final ID allocation.
//! - Neither mode relies on global locks; semantics are built per invocation
//!   and returned as immutable snapshots.

pub mod assoc;
pub mod js;
pub mod ts;
