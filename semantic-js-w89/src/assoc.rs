use crate::js::ScopeId;
use crate::js::SymbolId;
use parse_js::ast::node::NodeAssocData;

#[derive(Clone, Copy, Debug)]
pub struct DeclaredSymbol(pub SymbolId);

#[derive(Clone, Copy, Debug)]
pub struct ResolvedSymbol(pub Option<SymbolId>);

pub fn scope_id(assoc: &NodeAssocData) -> Option<ScopeId> {
  assoc.get::<ScopeId>().copied()
}

pub fn declared_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc.get::<DeclaredSymbol>().map(|d| d.0)
}

pub fn resolved_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc.get::<ResolvedSymbol>().and_then(|r| r.0)
}
