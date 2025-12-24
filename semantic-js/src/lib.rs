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
