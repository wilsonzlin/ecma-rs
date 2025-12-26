//! Per-body checking context backed by a bump allocator.
//!
//! `check_body` allocates many short-lived structures (facts, CFG worklists,
//! inference constraints). A dedicated arena per body keeps these allocations
//! fast and ensures they are freed as soon as the query completes.

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump;
use std::cell::RefCell;

use super::super::{
  BodyCheckResult, BodyId, BuiltinTypes, Diagnostic, ExprId, TextRange, TypeId, TypeStore,
};
use super::narrow::Facts;
use hir_js::PatId;

/// Mutable, per-body caches and reusable scratch buffers.
///
/// All data stored here is transient and dropped alongside the owning
/// [`BodyCheckCtx`]; anything that needs to escape the query must be written
/// into [`BodyCheckOutput`] instead.
pub(crate) struct BodyCaches {
  expr_types: RefCell<Vec<Option<TypeId>>>,
  pat_types: RefCell<Vec<Option<TypeId>>>,
  type_scratch: RefCell<Vec<TypeId>>,
}

impl BodyCaches {
  pub fn new(expr_len: usize, pat_len: usize) -> Self {
    BodyCaches {
      expr_types: RefCell::new(vec![None; expr_len]),
      pat_types: RefCell::new(vec![None; pat_len]),
      type_scratch: RefCell::new(Vec::new()),
    }
  }

  pub fn cache_expr_type(&self, expr: ExprId, ty: TypeId) {
    if let Some(slot) = self.expr_types.borrow_mut().get_mut(expr.0 as usize) {
      *slot = Some(ty);
    }
  }

  pub fn cache_pat_type(&self, pat: PatId, ty: TypeId) {
    if let Some(slot) = self.pat_types.borrow_mut().get_mut(pat.0 as usize) {
      *slot = Some(ty);
    }
  }

  #[allow(dead_code)]
  pub fn cached_expr_type(&self, expr: ExprId) -> Option<TypeId> {
    self
      .expr_types
      .borrow()
      .get(expr.0 as usize)
      .and_then(|t| *t)
  }

  #[allow(dead_code)]
  pub fn cached_pat_type(&self, pat: PatId) -> Option<TypeId> {
    self.pat_types.borrow().get(pat.0 as usize).and_then(|t| *t)
  }

  /// Provide a reusable scratch vector for short-lived operations within a
  /// body. The buffer is cleared before and after the callback to bound the
  /// growth of temporary allocations.
  #[allow(dead_code)]
  pub fn with_type_scratch<R>(&self, f: impl FnOnce(&mut Vec<TypeId>) -> R) -> R {
    let mut scratch = self.type_scratch.borrow_mut();
    scratch.clear();
    let result = f(&mut scratch);
    scratch.clear();
    result
  }

  /// Create a union using a shared scratch vector to avoid repeated allocations
  /// while checking a single body.
  pub fn union_from_iter(
    &self,
    store: &mut TypeStore,
    builtin: &BuiltinTypes,
    types: impl IntoIterator<Item = TypeId>,
  ) -> TypeId {
    self.with_type_scratch(|scratch| store.union_from_iter(types, builtin, scratch))
  }
}

/// Owned output of checking a single body.
pub(crate) struct BodyCheckOutput {
  pub body: BodyId,
  pub expr_types: Vec<TypeId>,
  pub expr_spans: Vec<TextRange>,
  pub pat_spans: Vec<TextRange>,
  pub pat_types: Vec<TypeId>,
  pub diagnostics: Vec<Diagnostic>,
  pub return_types: Vec<TypeId>,
  unknown: TypeId,
}

impl BodyCheckOutput {
  pub fn new(
    body: BodyId,
    expr_spans: &[TextRange],
    pat_spans: &[TextRange],
    unknown: TypeId,
  ) -> Self {
    BodyCheckOutput {
      body,
      expr_types: vec![unknown; expr_spans.len()],
      expr_spans: expr_spans.to_vec(),
      pat_spans: pat_spans.to_vec(),
      pat_types: Vec::with_capacity(pat_spans.len()),
      diagnostics: Vec::new(),
      return_types: Vec::new(),
      unknown,
    }
  }

  pub fn set_expr_type(&mut self, expr: ExprId, ty: TypeId) {
    if let Some(slot) = self.expr_types.get_mut(expr.0 as usize) {
      *slot = ty;
    }
  }

  pub fn set_pat_type(&mut self, pat: PatId, ty: TypeId) {
    let idx = pat.0 as usize;
    if self.pat_types.len() <= idx {
      self.pat_types.resize(idx + 1, self.unknown);
    }
    self.pat_types[idx] = ty;
  }

  pub fn push_pat_type(&mut self, ty: TypeId) {
    self.pat_types.push(ty);
  }

  pub fn into_result(self) -> BodyCheckResult {
    BodyCheckResult {
      body: self.body,
      expr_types: self.expr_types,
      expr_spans: self.expr_spans,
      pat_spans: self.pat_spans,
      pat_types: self.pat_types,
      diagnostics: self.diagnostics,
      return_types: self.return_types,
    }
  }
}

/// Ephemeral arena-backed context used while checking a single body.
pub(crate) struct BodyCheckCtx {
  pub bump: Bump,
  pub caches: BodyCaches,
  pub output: BodyCheckOutput,
}

impl BodyCheckCtx {
  pub fn new(
    body: BodyId,
    expr_spans: &[TextRange],
    pat_spans: &[TextRange],
    unknown: TypeId,
  ) -> Self {
    BodyCheckCtx {
      bump: Bump::new(),
      caches: BodyCaches::new(expr_spans.len(), pat_spans.len()),
      output: BodyCheckOutput::new(body, expr_spans, pat_spans, unknown),
    }
  }

  /// Fresh facts map allocated inside the arena.
  #[allow(dead_code)]
  pub fn new_facts(&self) -> Facts<'_> {
    Facts::new_in(&self.bump)
  }

  /// Scratch worklist allocated in the arena for CFG/narrowing/inference.
  #[allow(dead_code)]
  pub fn worklist<T>(&self) -> BumpVec<'_, T> {
    BumpVec::new_in(&self.bump)
  }

  pub fn into_result(self) -> BodyCheckResult {
    self.output.into_result()
  }
}
