use super::JsMode;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

impl ScopeId {
  pub(crate) fn idx(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
  pub(crate) fn idx(self) -> usize {
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
}

impl ScopeKind {
  pub fn is_closure(self) -> bool {
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
  pub symbols: HashMap<String, SymbolId>,
  pub children: Vec<ScopeId>,
}

impl ScopeData {
  pub fn symbol(&self, name: &str) -> Option<SymbolId> {
    self.symbols.get(name).copied()
  }
}

#[derive(Debug)]
pub struct SymbolData {
  pub id: SymbolId,
  pub name: String,
  pub declared_at: ScopeId,
}

#[derive(Debug)]
pub struct JsSemantics {
  pub(crate) scopes: Vec<ScopeData>,
  pub(crate) symbols: Vec<SymbolData>,
  root_scope: ScopeId,
  pub mode: JsMode,
}

impl JsSemantics {
  pub fn new(mode: JsMode) -> JsSemantics {
    let mut sem = JsSemantics {
      scopes: Vec::new(),
      symbols: Vec::new(),
      root_scope: ScopeId(0),
      mode,
    };
    let root_kind = match mode {
      JsMode::Global => ScopeKind::Global,
      JsMode::Module => ScopeKind::Module,
    };
    let root_scope = sem.push_scope_internal(None, root_kind);
    sem.root_scope = root_scope;
    sem
  }

  pub fn root_scope(&self) -> ScopeId {
    self.root_scope
  }

  pub fn scope(&self, id: ScopeId) -> &ScopeData {
    &self.scopes[id.idx()]
  }

  pub fn scope_mut(&mut self, id: ScopeId) -> &mut ScopeData {
    &mut self.scopes[id.idx()]
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    &self.symbols[id.idx()]
  }

  pub(crate) fn push_scope(&mut self, parent: ScopeId, kind: ScopeKind) -> ScopeId {
    self.push_scope_internal(Some(parent), kind)
  }

  fn push_scope_internal(&mut self, parent: Option<ScopeId>, kind: ScopeKind) -> ScopeId {
    let id = ScopeId(self.scopes.len() as u32);
    self.scopes.push(ScopeData {
      parent,
      kind,
      symbols: HashMap::new(),
      children: Vec::new(),
    });
    if let Some(parent) = parent {
      self.scope_mut(parent).children.push(id);
    }
    id
  }

  pub(crate) fn allocate_symbol(&mut self, declared_at: ScopeId, name: String) -> SymbolId {
    let id = SymbolId(self.symbols.len() as u32);
    self.symbols.push(SymbolData {
      id,
      name,
      declared_at,
    });
    id
  }
}
