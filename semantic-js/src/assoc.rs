use crate::js;
use crate::ts;
use parse_js::ast::node::NodeAssocData;

#[derive(Clone, Copy, Debug)]
pub struct DeclaredSymbol(pub js::SymbolId);

#[derive(Clone, Copy, Debug)]
pub struct ResolvedSymbol(pub Option<js::SymbolId>);

/// Associated TypeScript declared symbol for a node.
#[derive(Clone, Copy, Debug)]
pub struct TsDeclaredSymbol(pub ts::SymbolId);

/// Associated TypeScript resolved symbol for a node.
#[derive(Clone, Copy, Debug)]
pub struct TsResolvedSymbol(pub Option<ts::SymbolId>);

pub fn scope_id(assoc: &NodeAssocData) -> Option<js::ScopeId> {
  assoc.get::<js::ScopeId>().copied()
}

pub fn declared_symbol(assoc: &NodeAssocData) -> Option<js::SymbolId> {
  assoc.get::<DeclaredSymbol>().map(|d| d.0)
}

pub fn resolved_symbol(assoc: &NodeAssocData) -> Option<js::SymbolId> {
  assoc.get::<ResolvedSymbol>().and_then(|r| r.0)
}

/// Returns the associated TypeScript declared symbol ID for a node, if present.
pub fn ts_declared_symbol(assoc: &NodeAssocData) -> Option<ts::SymbolId> {
  assoc.get::<TsDeclaredSymbol>().map(|d| d.0)
}

/// Returns the associated TypeScript resolved symbol ID for a node, if present.
pub fn ts_resolved_symbol(assoc: &NodeAssocData) -> Option<ts::SymbolId> {
  assoc.get::<TsResolvedSymbol>().and_then(|r| r.0)
}
