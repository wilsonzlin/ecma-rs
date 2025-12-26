//! Association helpers for TS mode locals.
//!
//! These helper types/functions let consumers read TypeScript symbol and scope
//! IDs attached to the `parse-js` AST via `NodeAssocData`.

use super::SpanKey;
use crate::ts::locals::{ScopeId, SymbolId};
use derive_visitor::{Drive, DriveMut};
use diagnostics::TextRange;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::loc::Loc;
use std::collections::BTreeMap;

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

/// Immutable side tables produced by TS locals binding without AST mutation.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct TsAssocTables {
  pub scopes: BTreeMap<SpanKey, ScopeId>,
  pub declared: BTreeMap<SpanKey, SymbolId>,
  pub expr_resolutions: BTreeMap<SpanKey, SymbolId>,
  pub type_resolutions: BTreeMap<SpanKey, SymbolId>,
}

impl TsAssocTables {
  pub fn record_scope(&mut self, key: impl Into<SpanKey>, scope: ScopeId) {
    self.scopes.insert(key.into(), scope);
  }

  pub fn record_declared_symbol(&mut self, key: impl Into<SpanKey>, sym: SymbolId) {
    self.declared.insert(key.into(), sym);
  }

  pub fn record_expr_resolution(&mut self, key: impl Into<SpanKey>, sym: SymbolId) {
    self.expr_resolutions.insert(key.into(), sym);
  }

  pub fn record_type_resolution(&mut self, key: impl Into<SpanKey>, sym: SymbolId) {
    self.type_resolutions.insert(key.into(), sym);
  }

  pub fn scope(&self, key: impl Into<SpanKey>) -> Option<ScopeId> {
    self.scopes.get(&key.into()).copied()
  }

  pub fn declared_symbol(&self, key: impl Into<SpanKey>) -> Option<SymbolId> {
    self.declared.get(&key.into()).copied()
  }

  pub fn resolved_expr(&self, key: impl Into<SpanKey>) -> Option<SymbolId> {
    self.expr_resolutions.get(&key.into()).copied()
  }

  pub fn resolved_type(&self, key: impl Into<SpanKey>) -> Option<SymbolId> {
    self.type_resolutions.get(&key.into()).copied()
  }
}

pub fn scope_id_in_tables(tables: &TsAssocTables, loc: Loc) -> Option<ScopeId> {
  tables.scope(loc)
}

pub fn scope_id_for_range(tables: &TsAssocTables, range: TextRange) -> Option<ScopeId> {
  tables.scope(range)
}

pub fn declared_symbol_in_tables(tables: &TsAssocTables, range: TextRange) -> Option<SymbolId> {
  tables.declared_symbol(range)
}

pub fn resolved_symbol_in_tables(tables: &TsAssocTables, range: TextRange) -> Option<SymbolId> {
  tables.resolved_expr(range)
}

pub fn resolved_type_in_tables(tables: &TsAssocTables, range: TextRange) -> Option<SymbolId> {
  tables.resolved_type(range)
}

pub fn scope_id_for_node<S: Drive + DriveMut>(
  tables: &TsAssocTables,
  node: &Node<S>,
) -> Option<ScopeId> {
  tables.scope(node.loc)
}

pub fn declared_symbol_for_node<S: Drive + DriveMut>(
  tables: &TsAssocTables,
  node: &Node<S>,
) -> Option<SymbolId> {
  tables.declared_symbol(node.loc)
}
