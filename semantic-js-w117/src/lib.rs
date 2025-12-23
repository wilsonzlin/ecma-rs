use ahash::HashMap;
use std::str::FromStr;

pub mod js;
pub use js::declare::compute_semantic;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NameId(u32);

impl NameId {
  #[inline]
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SymbolId(u32);

impl SymbolId {
  #[inline]
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ScopeId(u32);

impl ScopeId {
  #[inline]
  pub fn index(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ScopeType {
  Global,
  Module,
  // Closure with `this` (property initialisers have access to it) but not `arguments`.
  Class,
  // Functions with `this` and `arguments`.
  NonArrowFunction,
  // Functions with neither `this` nor `arguments`.
  ArrowFunction,
  Block,
}

impl ScopeType {
  pub fn is_closure(&self) -> bool {
    matches!(
      self,
      ScopeType::Module | ScopeType::NonArrowFunction | ScopeType::ArrowFunction
    )
  }

  pub fn is_closure_or_class(&self) -> bool {
    matches!(
      self,
      ScopeType::Class | ScopeType::Module | ScopeType::NonArrowFunction | ScopeType::ArrowFunction
    )
  }

  pub fn is_closure_or_global(&self) -> bool {
    matches!(
      self,
      ScopeType::Global
        | ScopeType::Module
        | ScopeType::NonArrowFunction
        | ScopeType::ArrowFunction
    )
  }

  pub fn is_closure_or_block(&self) -> bool {
    matches!(
      self,
      ScopeType::Block | ScopeType::Module | ScopeType::NonArrowFunction | ScopeType::ArrowFunction
    )
  }
}

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

#[derive(Debug)]
pub struct SymbolData {
  pub name: NameId,
  pub scope: ScopeId,
}

#[derive(Debug)]
pub struct ScopeData {
  pub parent: Option<ScopeId>,
  pub children: Vec<ScopeId>,
  pub symbols: HashMap<NameId, SymbolId>,
  /// Declaration order for this scope; tracks the first time a name is declared.
  pub decl_order: Vec<SymbolId>,
  pub typ: ScopeType,
}

#[derive(Debug)]
pub struct SemanticModel {
  names: Vec<String>,
  name_lookup: HashMap<String, NameId>,
  symbols: Vec<SymbolData>,
  scopes: Vec<ScopeData>,
  root_scope: ScopeId,
}

impl SemanticModel {
  pub fn new(root_type: ScopeType) -> Self {
    let mut semantic = SemanticModel {
      names: Vec::new(),
      name_lookup: HashMap::default(),
      symbols: Vec::new(),
      scopes: Vec::new(),
      root_scope: ScopeId(0),
    };
    let root = semantic.create_scope(None, root_type);
    semantic.root_scope = root;
    semantic
  }

  pub fn root_scope(&self) -> ScopeId {
    self.root_scope
  }

  pub fn scope(&self, id: ScopeId) -> &ScopeData {
    &self.scopes[id.index()]
  }

  pub(crate) fn scope_mut(&mut self, id: ScopeId) -> &mut ScopeData {
    &mut self.scopes[id.index()]
  }

  /// Deterministic symbol order for the provided scope, reflecting the first
  /// time each name was declared.
  pub fn scope_symbols_in_order(&self, scope: ScopeId) -> &[SymbolId] {
    &self.scope(scope).decl_order
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    &self.symbols[id.index()]
  }

  pub fn symbol_name(&self, id: SymbolId) -> &str {
    let name = self.symbol(id).name;
    self.name(name)
  }

  pub fn name(&self, id: NameId) -> &str {
    &self.names[id.index()]
  }

  pub(crate) fn find_scope_upwards(
    &self,
    start: ScopeId,
    predicate: impl Fn(ScopeType) -> bool,
  ) -> Option<ScopeId> {
    let mut cur = Some(start);
    while let Some(scope) = cur {
      let data = self.scope(scope);
      if predicate(data.typ) {
        return Some(scope);
      }
      cur = data.parent;
    }
    None
  }

  pub(crate) fn declare_symbol(&mut self, scope: ScopeId, name: &str) -> SymbolId {
    let name_id = self.intern_name(name);
    self.declare_symbol_by_name_id(scope, name_id)
  }

  pub(crate) fn declare_symbol_by_name_id(&mut self, scope: ScopeId, name_id: NameId) -> SymbolId {
    if let Some(existing) = self.scope_mut(scope).symbols.get(&name_id).copied() {
      return existing;
    }

    let symbol_id = SymbolId(self.symbols.len() as u32);
    self.symbols.push(SymbolData {
      name: name_id,
      scope,
    });

    let scope_data = self.scope_mut(scope);
    scope_data.symbols.insert(name_id, symbol_id);
    scope_data.decl_order.push(symbol_id);
    symbol_id
  }

  pub(crate) fn create_scope(&mut self, parent: Option<ScopeId>, typ: ScopeType) -> ScopeId {
    let id = ScopeId(self.scopes.len() as u32);
    self.scopes.push(ScopeData {
      parent,
      children: Vec::new(),
      symbols: HashMap::default(),
      decl_order: Vec::new(),
      typ,
    });
    if let Some(parent_id) = parent {
      self.scope_mut(parent_id).children.push(id);
    }
    id
  }

  fn intern_name(&mut self, name: &str) -> NameId {
    if let Some(id) = self.name_lookup.get(name) {
      return *id;
    }
    let id = NameId(self.names.len() as u32);
    self.names.push(name.to_string());
    self.name_lookup.insert(name.to_string(), id);
    id
  }
}
