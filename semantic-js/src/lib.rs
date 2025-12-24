//! Unified JavaScript/TypeScript semantics shared across the workspace.
//!
//! `semantic-js` intentionally hosts two distinct entry points that share the
//! same determinism and lock-free goals:
//!
//! - [`js`] builds a lexical scope tree for JavaScript/TS syntax and attaches
//!   small identifiers (`ScopeId`, `DeclaredSymbol`, `ResolvedSymbol`) to
//!   [`parse_js::ast::node::NodeAssocData`] so downstream crates such as
//!   optimizers or minifiers can query scope information without owning the AST.
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
//!   lookups are stable, but iteration over internal `HashMap` tables is not
//!   guaranteed to be deterministic.
//! - TS mode exposes only ordered structures (`BTreeMap`, sorted declaration
//!   lists) in its public API; root ordering and resolver results still drive
//!   the final ID allocation.
//! - Neither mode relies on global locks; semantics are built per invocation
//!   and returned as immutable snapshots.
mod assoc;

pub mod js;
pub mod ts;

pub use assoc::declared_symbol;
pub use assoc::resolved_symbol;
pub use assoc::scope_id;
pub use assoc::ts_declared_symbol;
pub use assoc::ts_resolved_symbol;
pub use assoc::DeclaredSymbol;
pub use assoc::ResolvedSymbol;
pub use assoc::TsDeclaredSymbol;
pub use assoc::TsResolvedSymbol;
pub use js::bind_js;
pub use js::declare;
pub use js::resolve;
pub use js::JsResolution;
pub use js::JsSemantics;
pub use js::NameId;
pub use js::ScopeData;
pub use js::ScopeId;
pub use js::ScopeKind;
pub use js::SymbolData;
pub use js::SymbolId;
pub use js::TopLevelMode;
