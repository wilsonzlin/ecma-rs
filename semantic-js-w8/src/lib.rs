mod bind_js;
mod data;
mod intern;

pub use bind_js::bind_js;
pub use data::resolve_in_scope;
pub use data::symbol_at_offset;
pub use data::BoundFile;
pub use data::ScopeData;
pub use data::ScopeId;
pub use data::ScopeKind;
pub use data::SymbolData;
pub use data::SymbolFlags;
pub use data::SymbolId;
pub use data::SymbolKind;
pub use intern::NameId;
pub use intern::NameInterner;
pub use intern::NameTable;
