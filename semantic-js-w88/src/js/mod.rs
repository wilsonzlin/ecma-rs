use ahash::HashMap;
use std::str::FromStr;

pub mod declare;

pub use declare::declare;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TopLevelMode {
  Global,
  Module,
}

impl FromStr for TopLevelMode {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "global" | "Global" => Ok(TopLevelMode::Global),
      "module" | "Module" => Ok(TopLevelMode::Module),
      _ => Err(()),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId(u32);

impl ScopeId {
  pub(crate) fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(u32);

impl SymbolId {
  pub(crate) fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NameId(u32);

impl NameId {
  pub(crate) fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScopeKind {
  Global,
  Module,
  Class,
  NonArrowFunction,
  ArrowFunction,
  Block,
  FunctionExpressionName,
}

impl ScopeKind {
  pub(crate) fn is_closure(&self) -> bool {
    matches!(
      self,
      ScopeKind::Module | ScopeKind::NonArrowFunction | ScopeKind::ArrowFunction
    )
  }
}

#[derive(Debug)]
pub struct ScopeData {
  pub parent: Option<ScopeId>,
  pub kind: ScopeKind,
  pub children: Vec<ScopeId>,
  pub symbols: HashMap<NameId, SymbolId>,
}

impl ScopeData {
  pub fn get(&self, name: NameId) -> Option<SymbolId> {
    self.symbols.get(&name).copied()
  }
}

#[derive(Debug)]
pub struct SymbolData {
  pub name: NameId,
  pub decl_scope: ScopeId,
}

#[derive(Debug)]
pub struct JsSemantics {
  pub names: Vec<String>,
  pub scopes: Vec<ScopeData>,
  pub symbols: Vec<SymbolData>,
  pub top_scope: ScopeId,
}

impl JsSemantics {
  pub fn top_scope(&self) -> ScopeId {
    self.top_scope
  }

  pub fn scope(&self, id: ScopeId) -> &ScopeData {
    &self.scopes[id.index()]
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    &self.symbols[id.index()]
  }

  pub fn name(&self, id: NameId) -> &str {
    &self.names[id.index()]
  }

  pub fn name_id(&self, name: &str) -> Option<NameId> {
    self
      .names
      .iter()
      .position(|n| n == name)
      .map(|i| NameId(i as u32))
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeclaredSymbol(pub SymbolId);
