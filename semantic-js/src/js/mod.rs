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
//! - [`bind_js`] runs both passes and returns any binding diagnostics.
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
//!   are visible throughout that scope regardless of source order. Hoisted
//!   bindings for each scope are listed in [`ScopeData::hoisted_bindings`] so
//!   downstream passes can model the implicit `undefined` initialization.
//! - Temporal dead zones (TDZ): `let`/`const`/class declarations are recorded as
//!   TDZ bindings in their block scope; resolution marks uses as `in_tdz` until
//!   the binding is initialized.
//! - Dynamic scope hazards: scopes containing `with (...) { ... }` or direct
//!   calls to `eval(...)` are marked as dynamic so downstream consumers can
//!   avoid unsafe optimizations or renames.
//!
//! ## Determinism
//!
//! Scope, symbol, and name IDs are content-addressed using the file id, parent
//! scope, declaration kind, and source spans so the same source always produces
//! the same identifiers even when bound in parallel. Scope symbol tables use
//! [`std::collections::BTreeMap`] keyed by [`NameId`] so iteration is stable; use
//! [`ScopeData::iter_symbols_sorted`] or [`JsSemantics::scope_symbols`] to
//! traverse symbols deterministically.
use diagnostics::Diagnostic;
use diagnostics::FileId;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use std::collections::BTreeMap;
use std::str::FromStr;

pub mod declare;
pub mod resolve;

pub use declare::declare;
pub use resolve::resolve;
pub use resolve::JsResolution;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ScopeId(u64);

impl ScopeId {
  pub fn raw(self) -> u64 {
    self.0
  }

  pub fn from_raw(raw: u64) -> Self {
    ScopeId(raw)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(u64);

impl SymbolId {
  pub fn raw(self) -> u64 {
    self.0
  }

  pub fn from_raw(raw: u64) -> Self {
    SymbolId(raw)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(u64);

impl NameId {
  pub fn raw(self) -> u64 {
    self.0
  }

  pub fn from_raw(raw: u64) -> Self {
    NameId(raw)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScopeKind {
  Global,
  Module,
  Class,
  /// Class static initialization blocks (`static { ... }`).
  ///
  /// These blocks are always strict mode and introduce their own `var` scope,
  /// so `var` and function declarations do **not** leak outside the block.
  StaticBlock,
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

  pub(crate) fn is_var_scope(&self) -> bool {
    self.is_closure() || *self == ScopeKind::StaticBlock
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
  /// [`SymbolId`]s that are hoisted and initialized at the start of this scope.
  pub hoisted_bindings: Vec<SymbolId>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolFlags {
  /// True if the binding is hoisted to the start of its declaration scope.
  pub hoisted: bool,
  /// True if the binding is in the temporal dead zone until initialized.
  pub tdz: bool,
}

impl SymbolFlags {
  pub const fn new(hoisted: bool, tdz: bool) -> Self {
    Self { hoisted, tdz }
  }

  pub const fn hoisted() -> Self {
    Self {
      hoisted: true,
      tdz: false,
    }
  }

  pub const fn lexical_tdz() -> Self {
    Self {
      hoisted: false,
      tdz: true,
    }
  }

  pub fn union(self, other: SymbolFlags) -> SymbolFlags {
    SymbolFlags {
      hoisted: self.hoisted || other.hoisted,
      tdz: self.tdz || other.tdz,
    }
  }
}

impl Default for SymbolFlags {
  fn default() -> Self {
    SymbolFlags {
      hoisted: false,
      tdz: false,
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolData {
  pub name: NameId,
  pub decl_scope: ScopeId,
  pub flags: SymbolFlags,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsSemantics {
  /// Interned identifier strings keyed by stable [`NameId`]s.
  pub names: BTreeMap<NameId, String>,
  /// String → [`NameId`] lookup for deterministic resolution of raw names.
  pub name_lookup: BTreeMap<String, NameId>,
  pub scopes: BTreeMap<ScopeId, ScopeData>,
  pub symbols: BTreeMap<SymbolId, SymbolData>,
  pub top_scope: ScopeId,
}

impl JsSemantics {
  pub fn top_scope(&self) -> ScopeId {
    self.top_scope
  }

  pub fn scope(&self, id: ScopeId) -> &ScopeData {
    self.scopes.get(&id).expect("scope exists for id")
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    self.symbols.get(&id).expect("symbol exists for id")
  }

  pub fn symbol_flags(&self, id: SymbolId) -> SymbolFlags {
    self.symbol(id).flags
  }

  pub fn name(&self, id: NameId) -> &str {
    self
      .names
      .get(&id)
      .map(|s| s.as_str())
      .expect("name exists for id")
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

pub fn bind_js(
  top_level: &mut Node<TopLevel>,
  mode: TopLevelMode,
  file: FileId,
) -> (JsSemantics, Vec<Diagnostic>) {
  let (sem, mut diagnostics) = declare::declare_with_diagnostics(top_level, mode, file);
  let (_res, mut resolve_diagnostics) = resolve::resolve_with_diagnostics(top_level, &sem, file);
  diagnostics.append(&mut resolve_diagnostics);
  diagnostics::sort_diagnostics(&mut diagnostics);
  (sem, diagnostics)
}

#[cfg(test)]
mod tests;
