use parse_js::ast::node::NodeAssocData;

pub mod js;

pub use js::declare;
pub use js::DeclaredSymbol;
pub use js::JsSemantics;
pub use js::NameId;
pub use js::ScopeData;
pub use js::ScopeId;
pub use js::ScopeKind;
pub use js::SymbolData;
pub use js::SymbolId;
pub use js::TopLevelMode;

pub fn scope_id(assoc: &NodeAssocData) -> Option<ScopeId> {
  assoc.get::<ScopeId>().copied()
}
