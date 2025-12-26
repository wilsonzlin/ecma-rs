use diagnostics::FileId;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stx::TopLevel;
use semantic_js::assoc::js as assoc;
use semantic_js::js::{bind_js, JsResolution, JsSemantics, ScopeData, TopLevelMode};
use serde::Serialize;
use std::cmp::Ordering;

pub use semantic_js::js::ScopeKind;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct ScopeId(pub u64);

impl From<semantic_js::js::ScopeId> for ScopeId {
  fn from(value: semantic_js::js::ScopeId) -> Self {
    ScopeId(value.raw())
  }
}

impl ScopeId {
  pub fn raw_id(self) -> u64 {
    self.0
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct SymbolId(pub u64);

impl From<semantic_js::js::SymbolId> for SymbolId {
  fn from(value: semantic_js::js::SymbolId) -> Self {
    SymbolId(value.raw())
  }
}

impl SymbolId {
  pub fn raw_id(self) -> u64 {
    self.0 as u64
  }
}

impl PartialOrd for SymbolId {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for SymbolId {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

#[derive(Debug)]
pub struct JsSymbols {
  pub semantics: JsSemantics,
}

impl JsSymbols {
  pub fn bind(
    top_level: &mut Node<TopLevel>,
    mode: TopLevelMode,
    file: FileId,
  ) -> (Self, JsResolution) {
    let (semantics, resolution) = bind_js(top_level, mode, file);
    (Self { semantics }, resolution)
  }

  pub fn top_scope(&self) -> ScopeId {
    ScopeId::from(self.semantics.top_scope())
  }

  fn scope_data(&self, scope: ScopeId) -> &ScopeData {
    self
      .semantics
      .scopes
      .get(&semantic_js::js::ScopeId::from_raw(scope.0))
      .expect("scope available")
  }

  pub fn scope_kind(&self, scope: ScopeId) -> ScopeKind {
    self.scope_data(scope).kind
  }

  pub fn parent_scope(&self, scope: ScopeId) -> Option<ScopeId> {
    self.scope_data(scope).parent.map(Into::into)
  }

  pub fn children(&self, scope: ScopeId) -> impl Iterator<Item = ScopeId> + '_ {
    self
      .scope_data(scope)
      .children
      .iter()
      .copied()
      .map(Into::into)
  }

  pub fn symbol_decl_scope(&self, symbol: SymbolId) -> ScopeId {
    ScopeId::from(
      self
        .semantics
        .symbols
        .get(&semantic_js::js::SymbolId::from_raw(symbol.0))
        .expect("symbol present")
        .decl_scope,
    )
  }

  pub fn symbol_name(&self, symbol: SymbolId) -> &str {
    let data = self
      .semantics
      .symbols
      .get(&semantic_js::js::SymbolId::from_raw(symbol.0))
      .expect("symbol present");
    self.semantics.name(data.name)
  }

  /// Deterministically lists all symbols declared directly in `scope`.
  pub fn symbols_in_scope(&self, scope: ScopeId) -> Vec<(SymbolId, String)> {
    let mut symbols: Vec<_> = self
      .scope_data(scope)
      .symbols
      .iter()
      .map(|(name_id, symbol)| {
        (
          SymbolId::from(*symbol),
          self.semantics.name(*name_id).to_string(),
        )
      })
      .collect();
    symbols.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(&b.0)));
    symbols
  }
}

pub fn assoc_scope_id(assoc: &NodeAssocData) -> Option<ScopeId> {
  assoc::scope_id(assoc).map(Into::into)
}

pub fn assoc_declared_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc::declared_symbol(assoc).map(Into::into)
}

pub fn assoc_resolved_symbol(assoc: &NodeAssocData) -> Option<SymbolId> {
  assoc::resolved_symbol(assoc).map(Into::into)
}
