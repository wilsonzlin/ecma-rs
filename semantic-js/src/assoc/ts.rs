//! Association helpers for TS mode locals.
//!
//! These helper types/functions let consumers read TypeScript symbol and scope
//! IDs attached to the `parse-js` AST via `NodeAssocData`.

use crate::ts::locals::{ScopeId, SymbolId};
use parse_js::ast::node::NodeAssocData;

/// Declaration symbol attached by the TS binder.
#[derive(Clone, Copy, Debug)]
pub struct DeclaredSymbol(pub SymbolId);

/// Resolved symbol attached by the TS resolver.
#[derive(Clone, Copy, Debug)]
pub struct ResolvedSymbol(pub Option<SymbolId>);

/// Scope identifier attached to a node.
#[derive(Clone, Copy, Debug)]
pub struct ScopeInfo(pub ScopeId);

/// Declared symbol attached to the node, if any.
pub fn declared_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc.get::<DeclaredSymbol>().map(|d| d.0)
}

/// Resolved symbol attached to the node, if any.
pub fn resolved_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc.get::<ResolvedSymbol>().and_then(|r| r.0)
}

/// Scope ID attached to the node, if any.
pub fn scope_id(assoc: &NodeAssocData) -> Option<ScopeId> {
  assoc.get::<ScopeInfo>().map(|s| s.0)
}
