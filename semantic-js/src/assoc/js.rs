//! Association helpers for the JS semantics binder.
//!
//! These helper types/functions let consumers read semantic IDs that were
//! attached to the `parse-js` AST via `NodeAssocData`.

use crate::js::{ScopeId, SymbolId};
use parse_js::ast::node::NodeAssocData;

/// Declaration symbol attached by the JS binder.
#[derive(Clone, Copy, Debug)]
pub struct DeclaredSymbol(pub SymbolId);

/// Resolved symbol attached by the JS resolver.
#[derive(Clone, Copy, Debug)]
pub struct ResolvedSymbol(pub Option<SymbolId>);

/// Scope containing the node, if attached.
pub fn scope_id(assoc: &NodeAssocData) -> Option<ScopeId> {
  assoc.get::<ScopeId>().copied()
}

/// Declared symbol attached to the node, if any.
pub fn declared_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc.get::<DeclaredSymbol>().map(|d| d.0)
}

/// Resolved symbol attached to the node, if any.
pub fn resolved_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc.get::<ResolvedSymbol>().and_then(|r| r.0)
}
