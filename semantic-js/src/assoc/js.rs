//! Association helpers for the JS semantics binder.
//!
//! These helper types/functions let consumers read semantic IDs that were
//! attached to the `parse-js` AST via `NodeAssocData`.

use super::SpanKey;
use crate::js::{ScopeId, SymbolId};
use derive_visitor::{Drive, DriveMut};
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::loc::Loc;
use std::collections::BTreeMap;

/// Declaration symbol attached by the JS binder.
#[derive(Clone, Copy, Debug)]
pub struct DeclaredSymbol(pub SymbolId);

/// Resolved symbol attached by the JS resolver.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedSymbol {
  pub symbol: Option<SymbolId>,
  pub in_tdz: bool,
}

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
  assoc
    .get::<ResolvedSymbol>()
    .and_then(|ResolvedSymbol { symbol, .. }| *symbol)
}

/// Resolved symbol data attached to the node, if any.
pub fn resolved_symbol_info(assoc: &NodeAssocData) -> Option<ResolvedSymbol> {
  assoc.get::<ResolvedSymbol>().copied()
}

/// Immutable side tables produced by [`semantic_js::js::bind_js_pure`].
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct JsAssocTables {
  pub scopes: BTreeMap<SpanKey, ScopeId>,
  pub declared: BTreeMap<SpanKey, SymbolId>,
  pub resolved: BTreeMap<SpanKey, ResolvedSymbol>,
}

impl JsAssocTables {
  pub fn record_scope(&mut self, loc: Loc, scope: ScopeId) {
    self.scopes.insert(loc.into(), scope);
  }

  pub fn record_declared_symbol(&mut self, loc: Loc, symbol: SymbolId) {
    self.declared.insert(loc.into(), symbol);
  }

  pub fn record_resolved_symbol(&mut self, loc: Loc, symbol: Option<SymbolId>, in_tdz: bool) {
    self
      .resolved
      .insert(loc.into(), ResolvedSymbol { symbol, in_tdz });
  }

  pub fn scope(&self, key: impl Into<SpanKey>) -> Option<ScopeId> {
    self.scopes.get(&key.into()).copied()
  }

  pub fn declared_symbol(&self, key: impl Into<SpanKey>) -> Option<SymbolId> {
    self.declared.get(&key.into()).copied()
  }

  pub fn resolved_symbol(&self, key: impl Into<SpanKey>) -> Option<SymbolId> {
    self
      .resolved
      .get(&key.into())
      .and_then(|ResolvedSymbol { symbol, .. }| *symbol)
  }

  pub fn resolved_symbol_info(&self, key: impl Into<SpanKey>) -> Option<ResolvedSymbol> {
    self.resolved.get(&key.into()).copied()
  }
}

pub fn scope_id_in_tables(tables: &JsAssocTables, loc: Loc) -> Option<ScopeId> {
  tables.scope(loc)
}

pub fn declared_symbol_in_tables(tables: &JsAssocTables, loc: Loc) -> Option<SymbolId> {
  tables.declared_symbol(loc)
}

pub fn resolved_symbol_in_tables(tables: &JsAssocTables, loc: Loc) -> Option<SymbolId> {
  tables.resolved_symbol(loc)
}

pub fn resolved_symbol_info_in_tables(tables: &JsAssocTables, loc: Loc) -> Option<ResolvedSymbol> {
  tables.resolved_symbol_info(loc)
}

pub fn scope_id_for_node<S: Drive + DriveMut>(
  tables: &JsAssocTables,
  node: &Node<S>,
) -> Option<ScopeId> {
  scope_id_in_tables(tables, node.loc)
}

pub fn declared_symbol_for_node<S: Drive + DriveMut>(
  tables: &JsAssocTables,
  node: &Node<S>,
) -> Option<SymbolId> {
  declared_symbol_in_tables(tables, node.loc)
}

pub fn resolved_symbol_for_node<S: Drive + DriveMut>(
  tables: &JsAssocTables,
  node: &Node<S>,
) -> Option<SymbolId> {
  resolved_symbol_in_tables(tables, node.loc)
}

pub fn resolved_symbol_info_for_node<S: Drive + DriveMut>(
  tables: &JsAssocTables,
  node: &Node<S>,
) -> Option<ResolvedSymbol> {
  resolved_symbol_info_in_tables(tables, node.loc)
}
