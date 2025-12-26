//! JavaScript mode semantics: build a lexical scope tree and resolve identifiers
//! in the value namespace.
//!
//! This module builds scopes and symbols for plain JS inputs without TS
//! namespaces. After binding/resolving, use [`crate::assoc::js`] helpers to read
//! `ScopeId`/`SymbolId` attached to `parse-js` AST nodes.
//!
//! The JS entry points are intentionally small:
//! - [`declare()`] walks a parse-js AST, allocates [`ScopeId`]s and [`SymbolId`]s,
//!   and attaches the current [`ScopeId`] to every
//!   [`parse_js::ast::node::NodeAssocData`]. Declarations encountered in
//!   patterns receive [`crate::assoc::js::DeclaredSymbol`] handles.
//! - [`resolve()`] uses the attached [`ScopeId`]s to resolve identifier
//!   expressions and patterns to their nearest enclosing declaration and stores
//!   a [`crate::assoc::js::ResolvedSymbol`] next to the node.
//! - [`bind_js`] simply runs both passes.
//!
//! ## Scope kinds
//!
//! Scopes are hierarchical and stored in [`JsSemantics`] with stable indices:
//! - [`ScopeKind::Global`]: top-level in `"global"` [`TopLevelMode`]; top-level
//!   declarations are intentionally skipped so hosts can map globals separately.
//! - [`ScopeKind::Module`]: top-level in `"module"` [`TopLevelMode`]; acts as a
//!   closure for `var` declarations.
//! - [`ScopeKind::Class`]: class bodies.
//! - [`ScopeKind::NonArrowFunction`] / [`ScopeKind::ArrowFunction`]: function
//!   bodies; `var` hoists to the nearest of these or the module scope.
//! - [`ScopeKind::Block`]: block-scoped regions (including `for`/`catch`).
//! - [`ScopeKind::FunctionExpressionName`]: the dedicated scope for a named
//!   function expression's own name.
//!
//! ## Attachments and simplifications
//!
//! - Every AST node receives its enclosing [`ScopeId`] in `NodeAssocData`.
//! - Identifier patterns that introduce bindings receive
//!   [`crate::assoc::js::DeclaredSymbol`]; the same pattern positions without a
//!   declaration (e.g. destructuring assignment) are resolved as uses by
//!   [`resolve()`].
//! - Identifier expressions and non-decl patterns receive
//!   [`crate::assoc::js::ResolvedSymbol`] pointing to the nearest lexically
//!   visible declaration.
//! - Hoisting: `var` and function declarations bind to the nearest closure and
//!   are visible throughout that scope regardless of source order.
//! - Temporal dead zones (TDZ): `let`/`const`/class declarations are recorded as
//!   TDZ bindings in their block scope; resolution marks uses as `in_tdz` until
//!   the binding is initialized.
//! - Dynamic scope hazards: scopes containing `with (...) { ... }` or direct
//!   calls to `eval(...)` are marked as dynamic so downstream consumers can
//!   avoid unsafe optimizations or renames.
//!
//! ## Determinism caveats
//!
//! Scope and symbol IDs are allocated in traversal order and stored in `Vec`s.
//! Scope symbol tables use [`std::collections::BTreeMap`] keyed by [`NameId`]
//! so iteration is stable; use [`ScopeData::iter_symbols_sorted`] or
//! [`JsSemantics::scope_symbols`] to traverse symbols deterministically.
//! Names are interned in first-encounter order using a deterministic lookup map.
use crate::assoc::js::{DeclaredSymbol as LegacyDeclaredSymbol, JsAssocTables, ResolvedSymbol};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use std::collections::BTreeMap;
use std::str::FromStr;

pub mod declare;
pub mod resolve;

pub use declare::declare;
pub(crate) use declare::declare_with_assoc;
pub use resolve::resolve;
pub use resolve::JsResolution;
pub(crate) use resolve::resolve_with_assoc;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TopLevelMode {
  Global,
  Module,
}

pub(crate) trait JsAssocStore {
  fn record_scope(&mut self, loc: Loc, assoc: &mut NodeAssocData, scope: ScopeId);
  fn scope(&self, loc: Loc, assoc: &NodeAssocData) -> Option<ScopeId>;
  fn record_declared_symbol(&mut self, loc: Loc, assoc: &mut NodeAssocData, symbol: SymbolId);
  fn declared_symbol(&self, loc: Loc, assoc: &NodeAssocData) -> Option<SymbolId>;
  fn record_resolved_symbol(
    &mut self,
    loc: Loc,
    assoc: &mut NodeAssocData,
    symbol: Option<SymbolId>,
    in_tdz: bool,
  );
}

#[derive(Default)]
pub(crate) struct LegacyJsAssocStore;

impl JsAssocStore for LegacyJsAssocStore {
  fn record_scope(&mut self, _loc: Loc, assoc: &mut NodeAssocData, scope: ScopeId) {
    assoc.set(scope);
  }

  fn scope(&self, _loc: Loc, assoc: &NodeAssocData) -> Option<ScopeId> {
    assoc.get::<ScopeId>().copied()
  }

  fn record_declared_symbol(&mut self, _loc: Loc, assoc: &mut NodeAssocData, symbol: SymbolId) {
    assoc.set(LegacyDeclaredSymbol(symbol));
  }

  fn declared_symbol(&self, _loc: Loc, assoc: &NodeAssocData) -> Option<SymbolId> {
    assoc.get::<LegacyDeclaredSymbol>().map(|s| s.0)
  }

  fn record_resolved_symbol(
    &mut self,
    _loc: Loc,
    assoc: &mut NodeAssocData,
    symbol: Option<SymbolId>,
    in_tdz: bool,
  ) {
    assoc.set(ResolvedSymbol { symbol, in_tdz });
  }
}

pub(crate) struct TableJsAssocStore<'a> {
  tables: &'a mut JsAssocTables,
}

impl<'a> TableJsAssocStore<'a> {
  pub fn new(tables: &'a mut JsAssocTables) -> Self {
    Self { tables }
  }
}

impl JsAssocStore for TableJsAssocStore<'_> {
  fn record_scope(&mut self, loc: Loc, _assoc: &mut NodeAssocData, scope: ScopeId) {
    self.tables.record_scope(loc, scope);
  }

  fn scope(&self, loc: Loc, _assoc: &NodeAssocData) -> Option<ScopeId> {
    self.tables.scope(loc)
  }

  fn record_declared_symbol(&mut self, loc: Loc, _assoc: &mut NodeAssocData, symbol: SymbolId) {
    self.tables.record_declared_symbol(loc, symbol);
  }

  fn declared_symbol(&self, loc: Loc, _assoc: &NodeAssocData) -> Option<SymbolId> {
    self.tables.declared_symbol(loc)
  }

  fn record_resolved_symbol(
    &mut self,
    loc: Loc,
    _assoc: &mut NodeAssocData,
    symbol: Option<SymbolId>,
    in_tdz: bool,
  ) {
    self.tables.record_resolved_symbol(loc, symbol, in_tdz);
  }
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
  pub fn index(self) -> usize {
    self.0 as usize
  }

  pub fn raw(self) -> u32 {
    self.0
  }

  pub fn from_raw(raw: u32) -> Self {
    ScopeId(raw)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(u32);

impl SymbolId {
  pub fn index(self) -> usize {
    self.0 as usize
  }

  pub fn raw(self) -> u32 {
    self.0
  }

  pub fn from_raw(raw: u32) -> Self {
    SymbolId(raw)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(u32);

impl NameId {
  pub fn index(self) -> usize {
    self.0 as usize
  }

  pub fn raw(self) -> u32 {
    self.0
  }

  pub fn from_raw(raw: u32) -> Self {
    NameId(raw)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeData {
  pub parent: Option<ScopeId>,
  pub kind: ScopeKind,
  pub children: Vec<ScopeId>,
  pub symbols: BTreeMap<NameId, SymbolId>,
  /// Whether lookups in this scope may be affected by `with` or direct `eval`.
  pub is_dynamic: bool,
  /// True if a direct `eval(...)` call was found within this scope or its
  /// non-closure ancestors.
  pub has_direct_eval: bool,
  /// [`SymbolId`]s for lexical bindings that are in TDZ from the start of the
  /// scope until initialized.
  pub tdz_bindings: Vec<SymbolId>,
}

impl ScopeData {
  pub fn get(&self, name: NameId) -> Option<SymbolId> {
    self.symbols.get(&name).copied()
  }

  /// Iterates over symbols in deterministic [`NameId`] order.
  pub fn iter_symbols_sorted(&self) -> impl Iterator<Item = (NameId, SymbolId)> + '_ {
    self.symbols.iter().map(|(name, symbol)| (*name, *symbol))
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolData {
  pub name: NameId,
  pub decl_scope: ScopeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsSemantics {
  /// Interned identifier strings in order of first encounter.
  pub names: Vec<String>,
  /// String → [`NameId`] lookup for deterministic resolution of raw names.
  pub name_lookup: BTreeMap<String, NameId>,
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
    self.name_lookup.get(name).copied()
  }

  /// Resolves a [`NameId`] starting from `scope`, walking ancestor scopes until a
  /// symbol is found.
  pub fn resolve_name_id_in_scope(&self, scope: ScopeId, name: NameId) -> Option<SymbolId> {
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      let scope_data = self.scope(scope_id);
      if let Some(symbol) = scope_data.get(name) {
        return Some(symbol);
      }
      current = scope_data.parent;
    }
    None
  }

  /// Resolves a raw identifier string starting from `scope`.
  pub fn resolve_name_in_scope(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
    let Some(name_id) = self.name_id(name) else {
      return None;
    };
    self.resolve_name_id_in_scope(scope, name_id)
  }

  /// Deterministically iterates over `(NameId, SymbolId)` pairs within a scope.
  pub fn scope_symbols(&self, scope: ScopeId) -> impl Iterator<Item = (NameId, SymbolId)> + '_ {
    self.scope(scope).iter_symbols_sorted()
  }
}

/// Legacy binding entry point that mutates `NodeAssocData`.
/// Prefer [`bind_js_pure`] when running in parallel or in incremental contexts.
pub fn bind_js(top_level: &mut Node<TopLevel>, mode: TopLevelMode) -> (JsSemantics, JsResolution) {
  let mut assoc = LegacyJsAssocStore::default();
  bind_js_with_assoc(top_level, mode, &mut assoc)
}

/// Pure binding entry point that leaves the AST untouched and returns side tables
/// keyed by source spans.
pub fn bind_js_pure(
  top_level: &mut Node<TopLevel>,
  mode: TopLevelMode,
) -> (JsSemantics, JsAssocTables) {
  let mut tables = JsAssocTables::default();
  let (sem, _res) = {
    let mut assoc = TableJsAssocStore::new(&mut tables);
    bind_js_with_assoc(top_level, mode, &mut assoc)
  };
  (sem, tables)
}

fn bind_js_with_assoc(
  top_level: &mut Node<TopLevel>,
  mode: TopLevelMode,
  assoc: &mut impl JsAssocStore,
) -> (JsSemantics, JsResolution) {
  let sem = declare_with_assoc(top_level, mode, assoc);
  let res = resolve_with_assoc(top_level, &sem, assoc);
  (sem, res)
}

#[cfg(test)]
mod tests;
