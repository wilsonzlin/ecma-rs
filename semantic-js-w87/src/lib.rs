//! Deterministic scopes and symbols for JavaScript.
//!
//! This crate provides a small, lock-free semantic model for JavaScript mode
//! consumers. It focuses on deterministic arena indices and payload types that
//! can be attached to `parse-js` AST nodes without relying on global state or
//! runtime locks.

#![deny(missing_docs)]
#![forbid(unsafe_code)]

#[cfg(feature = "serde")]
use serde::Deserialize;
#[cfg(feature = "serde")]
use serde::Serialize;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::FromStr;

/// Whether the top-level acts as a global script or as an ES module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum TopLevelMode {
  /// The program runs in classic script mode and shares the host global scope.
  Global,
  /// The program runs as an ES module and has its own top-level scope.
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

impl TopLevelMode {
  /// Returns the [`ScopeKind`] that should be used for the top-level scope.
  pub const fn scope_kind(self) -> ScopeKind {
    match self {
      TopLevelMode::Global => ScopeKind::Global,
      TopLevelMode::Module => ScopeKind::Module,
    }
  }
}

/// Identifier for a scope stored inside [`JsSemantics`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ScopeId(u32);

impl ScopeId {
  /// The root scope allocated for a [`JsSemantics`] instance.
  pub const ROOT: ScopeId = ScopeId(0);

  /// Creates an identifier from its raw `u32` representation.
  pub const fn from_raw(raw: u32) -> ScopeId {
    ScopeId(raw)
  }

  /// Returns the underlying `u32` value for this identifier.
  pub const fn into_raw(self) -> u32 {
    self.0
  }

  fn new(index: usize) -> ScopeId {
    ScopeId(u32::try_from(index).expect("too many scopes for ScopeId"))
  }

  const fn index(self) -> usize {
    self.0 as usize
  }
}

/// Identifier for a symbol stored inside [`JsSemantics`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SymbolId(u32);

impl SymbolId {
  /// Creates an identifier from its raw `u32` representation.
  pub const fn from_raw(raw: u32) -> SymbolId {
    SymbolId(raw)
  }

  /// Returns the underlying `u32` value for this identifier.
  pub const fn into_raw(self) -> u32 {
    self.0
  }

  fn new(index: usize) -> SymbolId {
    SymbolId(u32::try_from(index).expect("too many symbols for SymbolId"))
  }

  const fn index(self) -> usize {
    self.0 as usize
  }
}

/// Identifier for an interned name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct NameId(u32);

impl NameId {
  /// Creates an identifier from its raw `u32` representation.
  pub const fn from_raw(raw: u32) -> NameId {
    NameId(raw)
  }

  /// Returns the underlying `u32` value for this identifier.
  pub const fn into_raw(self) -> u32 {
    self.0
  }

  fn new(index: usize) -> NameId {
    NameId(u32::try_from(index).expect("too many names for NameId"))
  }

  const fn index(self) -> usize {
    self.0 as usize
  }
}

/// Classification of a scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ScopeKind {
  /// The host/global script scope.
  Global,
  /// An ES module scope.
  Module,
  /// A class body (has its own `this`).
  Class,
  /// A non-arrow function with its own `this`/`arguments`.
  NonArrowFunction,
  /// An arrow function scope.
  ArrowFunction,
  /// A block scope (including loops, `catch`, etc.).
  Block,
}

impl ScopeKind {
  /// Returns `true` if this scope introduces a closure boundary.
  pub const fn is_closure(self) -> bool {
    matches!(
      self,
      ScopeKind::Module | ScopeKind::NonArrowFunction | ScopeKind::ArrowFunction
    )
  }

  /// Returns `true` if this scope behaves like a closure or a class.
  pub const fn is_closure_or_class(self) -> bool {
    matches!(self, ScopeKind::Class) || self.is_closure()
  }

  /// Returns `true` if this scope is the global scope or introduces a closure.
  pub const fn is_closure_or_global(self) -> bool {
    matches!(self, ScopeKind::Global) || self.is_closure()
  }

  /// Returns `true` if this scope is a closure or an ordinary block.
  pub const fn is_closure_or_block(self) -> bool {
    matches!(self, ScopeKind::Block) || self.is_closure()
  }
}

/// Interner for symbol and scope names.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct NameInterner {
  names: Vec<String>,
  index: HashMap<String, NameId>,
}

impl NameInterner {
  /// Creates an empty name interner.
  pub fn new() -> NameInterner {
    NameInterner::default()
  }

  /// Interns a string and returns its stable [`NameId`].
  pub fn intern(&mut self, name: impl AsRef<str>) -> NameId {
    let name = name.as_ref();
    if let Some(existing) = self.index.get(name) {
      return *existing;
    }

    let id = NameId::new(self.names.len());
    let owned = name.to_owned();
    self.names.push(owned.clone());
    self.index.insert(owned, id);
    id
  }

  /// Returns an existing [`NameId`] for `name` if it has already been interned.
  pub fn lookup(&self, name: impl AsRef<str>) -> Option<NameId> {
    self.index.get(name.as_ref()).copied()
  }

  /// Resolves a [`NameId`] back into the string it represents.
  pub fn resolve(&self, id: NameId) -> Option<&str> {
    self.names.get(id.index()).map(String::as_str)
  }

  /// Returns the number of unique names interned so far.
  pub fn len(&self) -> usize {
    self.names.len()
  }

  /// Returns `true` if no names have been interned.
  pub fn is_empty(&self) -> bool {
    self.names.is_empty()
  }
}

/// Metadata describing a symbol.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SymbolData {
  /// The interned name this symbol represents.
  pub name: NameId,
  /// The scope that owns the symbol.
  pub declared_in: ScopeId,
}

/// Metadata describing a scope.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ScopeData {
  /// Classification of the scope.
  pub kind: ScopeKind,
  /// Parent scope, if one exists.
  pub parent: Option<ScopeId>,
  /// Child scopes created directly within this scope, in insertion order.
  pub children: Vec<ScopeId>,
  /// Symbols declared in this scope, ordered by first declaration.
  pub symbols: Vec<SymbolId>,
  /// Mapping of symbol names declared directly in this scope.
  pub symbols_by_name: HashMap<NameId, SymbolId>,
}

impl ScopeData {
  fn new(kind: ScopeKind, parent: Option<ScopeId>) -> ScopeData {
    ScopeData {
      kind,
      parent,
      children: Vec::new(),
      symbols: Vec::new(),
      symbols_by_name: HashMap::new(),
    }
  }

  /// Returns the locally declared symbol for a given name, if any.
  pub fn symbol_named(&self, name: NameId) -> Option<SymbolId> {
    self.symbols_by_name.get(&name).copied()
  }
}

/// Immutable snapshot of scope and symbol data for a single program.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct JsSemantics {
  top_level_mode: TopLevelMode,
  scopes: Vec<ScopeData>,
  symbols: Vec<SymbolData>,
  names: NameInterner,
}

impl JsSemantics {
  /// Creates a new builder to populate semantic data.
  pub fn builder(mode: TopLevelMode) -> JsSemanticsBuilder {
    JsSemanticsBuilder::new(mode)
  }

  /// Returns the mode used for the top-level scope.
  pub const fn top_level_mode(&self) -> TopLevelMode {
    self.top_level_mode
  }

  /// Returns the identifier for the root scope.
  pub const fn top_level_scope(&self) -> ScopeId {
    ScopeId::ROOT
  }

  /// Returns all scopes stored in this semantics instance.
  pub fn scopes(&self) -> &[ScopeData] {
    &self.scopes
  }

  /// Returns all symbols stored in this semantics instance.
  pub fn symbols(&self) -> &[SymbolData] {
    &self.symbols
  }

  /// Returns the [`ScopeData`] for the provided identifier.
  pub fn scope(&self, id: ScopeId) -> Option<&ScopeData> {
    self.scopes.get(id.index())
  }

  /// Returns the [`SymbolData`] for the provided identifier.
  pub fn symbol(&self, id: SymbolId) -> Option<&SymbolData> {
    self.symbols.get(id.index())
  }

  /// Returns the interned string for a [`NameId`], if it exists.
  pub fn name(&self, id: NameId) -> Option<&str> {
    self.names.resolve(id)
  }

  /// Provides access to the underlying name interner.
  pub fn names(&self) -> &NameInterner {
    &self.names
  }

  /// Resolves a symbol by name within the given scope, walking through
  /// ancestors if needed.
  pub fn resolve_symbol(&self, scope: ScopeId, name: NameId) -> Option<SymbolId> {
    let mut cur = Some(scope);
    while let Some(scope_id) = cur {
      let scope_data = self.scopes.get(scope_id.index())?;
      if let Some(sym) = scope_data.symbol_named(name) {
        return Some(sym);
      }
      cur = scope_data.parent;
    }
    None
  }

  /// Resolves a symbol by string name, searching the provided scope and its
  /// ancestors. Does not intern unknown names.
  pub fn resolve_symbol_str(&self, scope: ScopeId, name: impl AsRef<str>) -> Option<SymbolId> {
    let name_id = self.names.lookup(name)?;
    self.resolve_symbol(scope, name_id)
  }
}

/// Builder that constructs [`JsSemantics`] in a single thread with deterministic IDs.
#[derive(Debug, Clone)]
pub struct JsSemanticsBuilder {
  top_level_mode: TopLevelMode,
  scopes: Vec<ScopeData>,
  symbols: Vec<SymbolData>,
  names: NameInterner,
}

impl JsSemanticsBuilder {
  /// Creates a new builder configured for the provided top-level mode.
  pub fn new(top_level_mode: TopLevelMode) -> JsSemanticsBuilder {
    let mut builder = JsSemanticsBuilder {
      top_level_mode,
      scopes: Vec::new(),
      symbols: Vec::new(),
      names: NameInterner::default(),
    };

    let root_kind = top_level_mode.scope_kind();
    builder.push_scope(None, root_kind);
    builder
  }

  /// Returns the identifier of the root scope created for this builder.
  pub const fn top_level_scope(&self) -> ScopeId {
    ScopeId::ROOT
  }

  /// Returns an immutable view of scopes built so far.
  pub fn scopes(&self) -> &[ScopeData] {
    &self.scopes
  }

  /// Returns an immutable view of symbols built so far.
  pub fn symbols(&self) -> &[SymbolData] {
    &self.symbols
  }

  /// Adds a new child scope beneath `parent` with the provided kind.
  pub fn add_scope(&mut self, parent: ScopeId, kind: ScopeKind) -> ScopeId {
    self.push_scope(Some(parent), kind)
  }

  /// Declares a symbol in the provided scope. If the name already exists in the
  /// scope the existing symbol is returned.
  pub fn declare_symbol(&mut self, scope: ScopeId, name: impl AsRef<str>) -> SymbolId {
    let name_id = self.names.intern(name);
    let existing = self
      .scopes
      .get(scope.index())
      .unwrap_or_else(|| panic!("invalid ScopeId {:?}", scope))
      .symbols_by_name
      .get(&name_id)
      .copied();

    if let Some(existing) = existing {
      return existing;
    }

    let symbol_id = self.push_symbol(SymbolData {
      name: name_id,
      declared_in: scope,
    });
    let scope_data = self
      .scopes
      .get_mut(scope.index())
      .expect("scope should exist when recording a symbol");
    scope_data.symbols_by_name.insert(name_id, symbol_id);
    scope_data.symbols.push(symbol_id);
    symbol_id
  }

  /// Finalizes the builder into an immutable [`JsSemantics`] snapshot.
  pub fn build(self) -> JsSemantics {
    JsSemantics {
      top_level_mode: self.top_level_mode,
      scopes: self.scopes,
      symbols: self.symbols,
      names: self.names,
    }
  }

  fn push_scope(&mut self, parent: Option<ScopeId>, kind: ScopeKind) -> ScopeId {
    let id = ScopeId::new(self.scopes.len());
    self.scopes.push(ScopeData::new(kind, parent));
    if let Some(parent) = parent {
      self
        .scopes
        .get_mut(parent.index())
        .expect("parent scope should exist")
        .children
        .push(id);
    }
    id
  }

  fn push_symbol(&mut self, data: SymbolData) -> SymbolId {
    let id = SymbolId::new(self.symbols.len());
    self.symbols.push(data);
    id
  }
}

/// Payload for associating a resolved symbol with a syntax node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ResolvedSymbol(pub Option<SymbolId>);

impl From<Option<SymbolId>> for ResolvedSymbol {
  fn from(value: Option<SymbolId>) -> Self {
    ResolvedSymbol(value)
  }
}

impl From<SymbolId> for ResolvedSymbol {
  fn from(value: SymbolId) -> Self {
    ResolvedSymbol(Some(value))
  }
}

/// Payload for associating the symbol declared by a syntax node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DeclaredSymbol(pub SymbolId);

impl From<SymbolId> for DeclaredSymbol {
  fn from(value: SymbolId) -> Self {
    DeclaredSymbol(value)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn assert_send_sync<T: Send + Sync>() {}

  #[test]
  fn name_interner_reuses_ids() {
    let mut interner = NameInterner::new();
    let first = interner.intern("alpha");
    let second = interner.intern("alpha");
    assert_eq!(first, second);
    assert_eq!(interner.resolve(first), Some("alpha"));
    assert_eq!(interner.len(), 1);
  }

  #[test]
  fn lookup_does_not_intern() {
    let mut interner = NameInterner::new();
    let id = interner.intern("alpha");
    assert_eq!(interner.lookup("alpha"), Some(id));
    assert_eq!(interner.lookup("beta"), None);
    // Ensure a lookup for an unknown name does not create a new entry.
    assert_eq!(interner.len(), 1);
  }

  #[test]
  fn builder_creates_scopes_and_symbols_deterministically() {
    let mut builder = JsSemantics::builder(TopLevelMode::Module);
    let root = builder.top_level_scope();
    let child = builder.add_scope(root, ScopeKind::Block);
    let foo = builder.declare_symbol(root, "foo");
    let bar = builder.declare_symbol(child, "bar");
    let repeat = builder.declare_symbol(child, "bar");
    assert_eq!(bar, repeat);

    let semantics = builder.build();
    let root_scope = semantics.scope(root).unwrap();
    assert_eq!(root_scope.kind, ScopeKind::Module);
    assert_eq!(root_scope.children, vec![child]);
    assert_eq!(root_scope.symbols, vec![foo]);

    let child_scope = semantics.scope(child).unwrap();
    assert_eq!(child_scope.parent, Some(root));
    assert_eq!(child_scope.symbols, vec![bar]);

    let foo_data = semantics.symbol(foo).unwrap();
    assert_eq!(foo_data.declared_in, root);
    assert_eq!(semantics.name(foo_data.name), Some("foo"));
  }

  #[test]
  fn resolution_walks_parents() {
    let mut builder = JsSemantics::builder(TopLevelMode::Global);
    let root = builder.top_level_scope();
    let child = builder.add_scope(root, ScopeKind::Block);
    let foo = builder.declare_symbol(root, "foo");
    let bar = builder.declare_symbol(child, "bar");
    let semantics = builder.build();

    let foo_name = semantics.symbol(foo).unwrap().name;
    let bar_name = semantics.symbol(bar).unwrap().name;

    assert_eq!(semantics.resolve_symbol(child, foo_name), Some(foo));
    assert_eq!(semantics.resolve_symbol(child, bar_name), Some(bar));
    assert_eq!(semantics.resolve_symbol(root, bar_name), None);

    assert_eq!(semantics.resolve_symbol_str(child, "foo"), Some(foo));
    assert_eq!(semantics.resolve_symbol_str(child, "bar"), Some(bar));
    assert_eq!(semantics.resolve_symbol_str(root, "bar"), None);
    assert_eq!(semantics.resolve_symbol_str(root, "missing"), None);
    // Unknown lookups must not intern new names.
    assert_eq!(semantics.names().len(), 2);
  }

  #[test]
  fn payloads_are_send_sync() {
    assert_send_sync::<ResolvedSymbol>();
    assert_send_sync::<DeclaredSymbol>();
    assert_send_sync::<JsSemantics>();
  }
}
