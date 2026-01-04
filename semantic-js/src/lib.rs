//! Unified JavaScript/TypeScript semantics shared across the workspace.
//!
//! The public API is split by language mode to keep JS-only identifiers from
//! colliding with TypeScript counterparts:
//! - [`js`]: JS-only scopes and symbols used by optimizers/minifiers.
//! - [`ts`]: TypeScript binder and model (work in progress).
//! - [`assoc`]: Helpers for reading IDs attached to `parse-js` AST nodes.
//!
//! `semantic-js` intentionally hosts two distinct entry points that share the
//! same determinism and lock-free goals:
//!
//! - [`js`] builds a lexical scope tree for JavaScript/TS syntax and attaches
//!   small identifiers to [`parse_js::ast::node::NodeAssocData`] so downstream
//!   crates such as optimizers or minifiers can query scope information without
//!   owning the AST.
//! - [`ts`] binds module-level TypeScript declarations from lowered
//!   [`ts::HirFile`] inputs, producing deterministic symbol groups and export
//!   maps for consumption by a type checker or any consumer that needs
//!   TypeScript-aware module graphs.
//!
//! Both modes avoid global locks and allocate stable, content-addressed
//! identifiers so callers see the same IDs regardless of traversal order.
//!
//! ## JS mode quickstart
//!
//! Bind and resolve a `parse-js` AST, then read scope/symbol IDs via the helper
//! accessors:
//!
//! ```
//! use std::collections::HashMap;
//!
//! use derive_visitor::{DriveMut, VisitorMut};
//! use parse_js::{
//!   ast::{
//!     expr::{pat::IdPat, IdExpr},
//!     node::Node,
//!   },
//!   parse,
//! };
//! use semantic_js::{
//!   assoc::js::{declared_symbol, resolved_symbol, scope_id},
//!   js::{bind_js, ScopeId, SymbolId, TopLevelMode},
//! };
//!
//! type IdExprNode = Node<IdExpr>;
//! type IdPatNode = Node<IdPat>;
//!
//! #[derive(Default, VisitorMut)]
//! #[visitor(IdPatNode(enter), IdExprNode(enter))]
//! struct Collect {
//!   decls: HashMap<String, (ScopeId, SymbolId)>,
//!   uses: Vec<(String, ScopeId, Option<SymbolId>)>,
//! }
//!
//! impl Collect {
//!   fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
//!     let scope = scope_id(&node.assoc).expect("scope attached");
//!     if let Some(symbol) = declared_symbol(&node.assoc) {
//!       self.decls.insert(node.stx.name.clone(), (scope, symbol));
//!     }
//!   }
//!
//!   fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
//!     let scope = scope_id(&node.assoc).expect("scope attached");
//!     self
//!       .uses
//!       .push((node.stx.name.clone(), scope, resolved_symbol(&node.assoc)));
//!   }
//! }
//!
//! let mut ast = parse(
//!   r#"
//!     const top = 1;
//!     const make = () => {
//!       let inner = top;
//!       return inner;
//!     };
//!     make();
//!   "#,
//! )
//! .unwrap();
//!
//! let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, diagnostics::FileId(0));
//! assert!(diagnostics.is_empty());
//!
//! let mut collect = Collect::default();
//! ast.drive_mut(&mut collect);
//!
//! // Every identifier expression resolves back to its declaration symbol.
//! for (name, _, resolved) in &collect.uses {
//!   let (decl_scope, decl_symbol) = collect.decls.get(name).expect("declaration exists");
//!   assert_eq!(resolved, &Some(*decl_symbol));
//!   assert_eq!(sem.symbol(resolved.unwrap()).decl_scope, *decl_scope);
//! }
//!
//! let top_scope = sem.top_scope();
//! assert_eq!(collect.decls["top"].0, top_scope);
//! assert_ne!(collect.decls["inner"].0, top_scope);
//!
//! // Scope iteration is deterministic (ordered by NameId).
//! let top_symbols: Vec<_> = sem
//!   .scope_symbols(top_scope)
//!   .map(|(name, symbol)| (sem.name(name).to_string(), symbol.raw()))
//!   .collect();
//! assert_eq!(
//!   top_symbols,
//!   vec![
//!     ("top".to_string(), collect.decls["top"].1.raw()),
//!     ("make".to_string(), collect.decls["make"].1.raw())
//!   ]
//! );
//! ```
//!
//! ## Determinism and integration notes
//!
//! - JS mode writes attachments into [`parse_js::ast::node::NodeAssocData`];
//!   scope symbol iteration is deterministic via [`js::ScopeData::iter_symbols_sorted`]
//!   or [`js::JsSemantics::scope_symbols`].
//! - TS mode exposes only ordered structures (`BTreeMap`, sorted declaration
//!   lists) in its public API; root ordering and resolver results still drive
//!   the final ID allocation.
//! - Neither mode relies on global locks; semantics are built per invocation
//!   and returned as immutable snapshots.

pub mod assoc;
pub(crate) mod hash;
pub mod js;
pub mod ts;
