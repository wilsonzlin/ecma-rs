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
//! - The pass operates purely syntactically: it does not attempt to model
//!   hoisting, TDZ errors, `with`/`eval` semantics, or re-declaration
//!   diagnostics. `var` simply targets the nearest closure, and top-level
//!   bindings can be skipped entirely via [`TopLevelMode::Global`].
//!
//! ## Determinism caveats
//!
//! Scope and symbol IDs are allocated in traversal order and stored in `Vec`s.
//! Lookups are deterministic, but [`ScopeData::symbols`] uses `ahash::HashMap`
//! with a random state; iterating over it is not stable across runs. Downstream
//! code should rely on lookups by [`NameId`] or provide its own deterministic
//! ordering when exposing results publicly.
use ahash::HashMap;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
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

pub fn bind_js(top_level: &mut Node<TopLevel>, mode: TopLevelMode) -> (JsSemantics, JsResolution) {
  let sem = declare(top_level, mode);
  let res = resolve(top_level, &sem);
  (sem, res)
}

#[cfg(test)]
mod tests;
