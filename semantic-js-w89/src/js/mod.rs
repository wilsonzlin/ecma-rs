use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;

mod bind;
mod resolve;
pub mod semantics;

pub use bind::bind as bind_semantics;
pub use resolve::resolve;
pub use resolve::JsResolution;
pub use semantics::JsSemantics;
pub use semantics::ScopeData;
pub use semantics::ScopeId;
pub use semantics::ScopeKind;
pub use semantics::SymbolData;
pub use semantics::SymbolId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsMode {
  Global,
  Module,
}

pub fn bind_js(top_level: &mut Node<TopLevel>, mode: JsMode) -> (JsSemantics, JsResolution) {
  let sem = bind_semantics(top_level, mode);
  let res = resolve(top_level, &sem);
  (sem, res)
}

#[cfg(test)]
mod tests;
