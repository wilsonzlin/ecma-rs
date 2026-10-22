use crate::cache::{CacheConfig, CacheStats, ShardedCache};
use crate::ids::{DefId, ObjectId, TypeId, TypeParamId};
use crate::kind::{
  IntrinsicKind, MappedModifier, MappedType, TemplateChunk, TemplateLiteralType, TypeKind,
};
use crate::relate::RelateCtx;
use crate::shape::{PropData, PropKey, Property, Shape};
use crate::store::TypeStore;
use ahash::{AHashMap, AHashSet};
use ordered_float::OrderedFloat;
use smallvec::SmallVec;
use std::cmp::Ordering;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::Arc;

#[cfg(feature = "tracing")]
fn cache_stats_delta(before: CacheStats, after: CacheStats) -> CacheStats {
  CacheStats {
    hits: after.hits.saturating_sub(before.hits),
    misses: after.misses.saturating_sub(before.misses),
    insertions: after.insertions.saturating_sub(before.insertions),
    evictions: after.evictions.saturating_sub(before.evictions),
  }
}

/// Expanded representation of a referenced type definition.
///
/// The `params` field lists formal type parameters that should be
/// substituted with the caller-provided type arguments when evaluating the
/// expanded `ty`.
#[derive(Clone, Debug)]
pub struct ExpandedType {
  pub params: Vec<TypeParamId>,
  pub ty: TypeId,
}

/// Provides lazy expansion of `TypeKind::Ref` nodes.
pub trait TypeExpander {
  /// Expand a referenced definition. Implementations may return `None` to
  /// indicate that the definition is unknown; in that case, the evaluator
  /// will leave the reference unexpanded.
  ///
  /// Implementations are expected to be pure; cycle detection and memoization
  /// are handled by [`TypeEvaluator`].
  fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType>;
}

pub(crate) trait ConditionalAssignability {
  fn is_assignable_for_conditional(&self, src: TypeId, dst: TypeId) -> bool;
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct Substitution {
  bindings: Vec<(TypeParamId, TypeId)>,
}

impl Substitution {
  fn empty() -> Self {
    Self {
      bindings: Vec::new(),
    }
  }

  fn get(&self, param: TypeParamId) -> Option<TypeId> {
    self
      .bindings
      .binary_search_by_key(&param, |(p, _)| *p)
      .ok()
      .map(|idx| self.bindings[idx].1)
  }

  fn with(&self, param: TypeParamId, ty: TypeId) -> Self {
    let mut bindings = self.bindings.clone();
    match bindings.binary_search_by_key(&param, |(p, _)| *p) {
      Ok(idx) => bindings[idx] = (param, ty),
      Err(idx) => bindings.insert(idx, (param, ty)),
    };
    Self { bindings }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct EvalKey {
  gen: u64,
  ty: TypeId,
  subst: Substitution,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RefKey {
  gen: u64,
  def: DefId,
  args: SmallVec<[TypeId; 4]>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Key {
  Literal(PropKey),
  String,
  Number,
  Symbol,
}

impl Key {
  fn cmp(&self, other: &Self, store: &TypeStore) -> Ordering {
    let discr = self.discriminant().cmp(&other.discriminant());
    if discr != Ordering::Equal {
      return discr;
    }
    match (self, other) {
      (Key::Literal(a), Key::Literal(b)) => store.compare_prop_keys(a, b),
      _ => Ordering::Equal,
    }
  }

  fn discriminant(&self) -> u8 {
    match self {
      Key::Literal(PropKey::String(_)) => 0,
      Key::Literal(PropKey::Number(_)) => 1,
      Key::Literal(PropKey::Symbol(_)) => 2,
      Key::String => 3,
      Key::Number => 4,
      Key::Symbol => 5,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum KeySet {
  Known(Vec<Key>),
  Unknown,
}

impl KeySet {
  fn known(mut keys: Vec<Key>, store: &TypeStore) -> Self {
    keys.sort_by(|a, b| a.cmp(b, store));
    keys.dedup();
    KeySet::Known(keys)
  }

  fn union(self, other: Self, store: &TypeStore) -> Self {
    match (self, other) {
      (KeySet::Known(mut a), KeySet::Known(mut b)) => {
        a.append(&mut b);
        KeySet::known(a, store)
      }
      _ => KeySet::Unknown,
    }
  }

  fn intersect(self, other: Self, store: &TypeStore) -> Self {
    match (self, other) {
      // `Unknown` represents the broadest `keyof` result (`string | number | symbol`).
      // When intersecting keys (e.g. `keyof (A | B)`), that acts like a universal
      // set: intersecting it with a concrete key set yields the concrete set.
      (KeySet::Unknown, other) | (other, KeySet::Unknown) => other,
      (KeySet::Known(a), KeySet::Known(b)) => {
        let a_set: AHashSet<Key> = a.iter().cloned().collect();
        let b_set: AHashSet<Key> = b.iter().cloned().collect();

        let a_has_string = a_set.contains(&Key::String);
        let a_has_number = a_set.contains(&Key::Number);
        let a_has_symbol = a_set.contains(&Key::Symbol);
        let b_has_string = b_set.contains(&Key::String);
        let b_has_number = b_set.contains(&Key::Number);
        let b_has_symbol = b_set.contains(&Key::Symbol);

        let literal_in_set =
          |key: &Key, set: &AHashSet<Key>, has_string: bool, has_number: bool, has_symbol: bool| {
            match key {
              Key::Literal(PropKey::String(_)) => has_string || set.contains(key),
              Key::Literal(PropKey::Number(_)) => has_number || set.contains(key),
              Key::Literal(PropKey::Symbol(_)) => has_symbol || set.contains(key),
              _ => set.contains(key),
            }
          };

        // Build candidates from all literal keys that appear in either set, then
        // keep those that are present in both sets. Broad keys (`string`,
        // `number`, `symbol`) are handled separately below.
        let mut out = Vec::new();
        for key in a
          .iter()
          .chain(b.iter())
          .filter(|key| matches!(key, Key::Literal(_)))
        {
          if literal_in_set(key, &a_set, a_has_string, a_has_number, a_has_symbol)
            && literal_in_set(key, &b_set, b_has_string, b_has_number, b_has_symbol)
          {
            out.push(key.clone());
          }
        }

        if a_has_string && b_has_string {
          out.push(Key::String);
        }
        if a_has_number && b_has_number {
          out.push(Key::Number);
        }
        if a_has_symbol && b_has_symbol {
          out.push(Key::Symbol);
        }

        KeySet::known(out, store)
      }
    }
  }
}

#[derive(Clone, Debug)]
struct KeyInfo {
  key: Key,
  optional: bool,
  readonly: bool,
}

#[derive(Clone, Debug, Default)]
pub struct EvaluatorCacheStats {
  pub eval: CacheStats,
  pub references: CacheStats,
}

#[derive(Clone, Debug)]
pub struct EvaluatorCaches {
  generation: Arc<AtomicU64>,
  eval: Arc<ShardedCache<EvalKey, TypeId>>,
  refs: Arc<ShardedCache<RefKey, TypeId>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvaluatorLimits {
  pub depth_limit: usize,
  pub step_limit: usize,
  pub max_template_strings: usize,
}

impl EvaluatorLimits {
  pub const DEFAULT_DEPTH_LIMIT: usize = 64;
  pub const DEFAULT_MAX_TEMPLATE_STRINGS: usize = 1024;
  /// Sentinel that disables step tracking entirely.
  pub const UNLIMITED_STEP_LIMIT: usize = usize::MAX;
  /// Matches [`crate::RelationLimits::DEFAULT_STEP_LIMIT`].
  pub const DEFAULT_STEP_LIMIT: usize = 50_000;
}

impl Default for EvaluatorLimits {
  fn default() -> Self {
    Self {
      depth_limit: Self::DEFAULT_DEPTH_LIMIT,
      step_limit: Self::DEFAULT_STEP_LIMIT,
      max_template_strings: Self::DEFAULT_MAX_TEMPLATE_STRINGS,
    }
  }
}

impl EvaluatorCaches {
  pub fn new(config: CacheConfig) -> Self {
    Self {
      generation: Arc::new(AtomicU64::new(0)),
      eval: Arc::new(ShardedCache::new(config)),
      refs: Arc::new(ShardedCache::new(config)),
    }
  }

  pub fn invalidate(&self) {
    self.generation.fetch_add(1, AtomicOrdering::Relaxed);
  }

  pub fn stats(&self) -> EvaluatorCacheStats {
    EvaluatorCacheStats {
      eval: self.eval.stats(),
      references: self.refs.stats(),
    }
  }

  pub fn get_ref(&self, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    let key = RefKey {
      gen: self.generation.load(AtomicOrdering::Relaxed),
      def,
      args: SmallVec::from_slice(args),
    };
    self.refs.get(&key)
  }

  pub fn insert_ref(&self, def: DefId, args: &[TypeId], value: TypeId) {
    let key = RefKey {
      gen: self.generation.load(AtomicOrdering::Relaxed),
      def,
      args: SmallVec::from_slice(args),
    };
    self.refs.insert(key, value);
  }

  pub fn clear(&self) {
    self.eval.clear();
    self.refs.clear();
  }
}

/// Evaluates and canonicalizes types with support for lazy reference expansion
/// and TypeScript-style operators (conditional/mapped/template/indexed/keyof).
pub struct TypeEvaluator<'a, E: TypeExpander> {
  store: Arc<TypeStore>,
  expander: &'a E,
  conditional_assignability: Option<&'a dyn ConditionalAssignability>,
  default_conditional_assignability: Option<RelateCtx<'static>>,
  caches: EvaluatorCaches,
  eval_in_progress: AHashSet<EvalKey>,
  ref_in_progress: AHashSet<RefKey>,
  /// Per-`evaluate_ref`-invocation memo for `substitute_only`. Interned types
  /// are DAGs; a substitution walk without sharing explodes exponentially on
  /// self-similar types (e.g. `OldDiff<keyof this, _>` intersections whose
  /// members repeat the same ladder).
  subst_memo: std::collections::HashMap<TypeId, TypeId>,
  limits: EvaluatorLimits,
  steps: usize,
  /// Cooperative stop flag (e.g. host cancellation). Never panics.
  should_stop: Option<&'a std::sync::atomic::AtomicBool>,
  budget_exceeded: bool,
}

impl<'a, E: TypeExpander> std::fmt::Debug for TypeEvaluator<'a, E> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TypeEvaluator")
      .field("limits", &self.limits)
      .field("steps", &self.steps)
      .finish()
  }
}

impl<'a, E: TypeExpander> TypeEvaluator<'a, E> {
  fn has_free_type_param(
    &self,
    ty: TypeId,
    bound: &mut Vec<TypeParamId>,
    visited: &mut AHashSet<TypeId>,
    depth: usize,
  ) -> bool {
    if depth >= self.limits.depth_limit {
      // Depth-limit hits are treated conservatively so we don't incorrectly
      // collapse conditional types when a free type parameter exists behind a
      // recursive type graph.
      return true;
    }

    let kind = self.store.type_kind(ty);
    if let TypeKind::TypeParam(param) = kind {
      return !bound.contains(&param);
    }

    if !visited.insert(ty) {
      return false;
    }

    let result = match kind {
      TypeKind::Infer { constraint, .. } => constraint
        .map(|c| self.has_free_type_param(c, bound, visited, depth + 1))
        .unwrap_or(false),
      TypeKind::Tuple(elems) => elems
        .into_iter()
        .any(|elem| self.has_free_type_param(elem.ty, bound, visited, depth + 1)),
      TypeKind::Array { ty, .. } => self.has_free_type_param(ty, bound, visited, depth + 1),
      TypeKind::Union(members) => members
        .into_iter()
        .any(|member| self.has_free_type_param(member, bound, visited, depth + 1)),
      TypeKind::Intersection(members) => members
        .into_iter()
        .any(|member| self.has_free_type_param(member, bound, visited, depth + 1)),
      TypeKind::Object(obj) => {
        let object = self.store.object(obj);
        let shape = self.store.shape(object.shape);

        shape
          .properties
          .into_iter()
          .any(|prop| self.has_free_type_param(prop.data.ty, bound, visited, depth + 1))
          || shape.indexers.into_iter().any(|idxer| {
            self.has_free_type_param(idxer.key_type, bound, visited, depth + 1)
              || self.has_free_type_param(idxer.value_type, bound, visited, depth + 1)
          })
          || shape
            .call_signatures
            .into_iter()
            .any(|sig| self.signature_has_free_type_param(sig, bound, visited, depth + 1))
          || shape
            .construct_signatures
            .into_iter()
            .any(|sig| self.signature_has_free_type_param(sig, bound, visited, depth + 1))
      }
      TypeKind::Callable { overloads } => overloads
        .into_iter()
        .any(|sig| self.signature_has_free_type_param(sig, bound, visited, depth + 1)),
      TypeKind::Ref { args, .. } => args
        .into_iter()
        .any(|arg| self.has_free_type_param(arg, bound, visited, depth + 1)),
      TypeKind::Predicate { asserted, .. } => asserted
        .map(|ty| self.has_free_type_param(ty, bound, visited, depth + 1))
        .unwrap_or(false),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        ..
      } => {
        self.has_free_type_param(check, bound, visited, depth + 1)
          || self.has_free_type_param(extends, bound, visited, depth + 1)
          || self.has_free_type_param(true_ty, bound, visited, depth + 1)
          || self.has_free_type_param(false_ty, bound, visited, depth + 1)
      }
      TypeKind::Mapped(mapped) => {
        let free_in_source = self.has_free_type_param(mapped.source, bound, visited, depth + 1);

        let bound_len = bound.len();
        bound.push(mapped.param);
        let free_in_value = self.has_free_type_param(mapped.value, bound, visited, depth + 1)
          || mapped
            .name_type
            .map(|ty| self.has_free_type_param(ty, bound, visited, depth + 1))
            .unwrap_or(false)
          || mapped
            .as_type
            .map(|ty| self.has_free_type_param(ty, bound, visited, depth + 1))
            .unwrap_or(false);
        bound.truncate(bound_len);

        free_in_source || free_in_value
      }
      TypeKind::TemplateLiteral(tpl) => tpl
        .spans
        .into_iter()
        .any(|chunk| self.has_free_type_param(chunk.ty, bound, visited, depth + 1)),
      TypeKind::Intrinsic { ty, .. } => self.has_free_type_param(ty, bound, visited, depth + 1),
      TypeKind::IndexedAccess { obj, index } => {
        self.has_free_type_param(obj, bound, visited, depth + 1)
          || self.has_free_type_param(index, bound, visited, depth + 1)
      }
      TypeKind::KeyOf(inner) => self.has_free_type_param(inner, bound, visited, depth + 1),
      _ => false,
    };

    visited.remove(&ty);
    result
  }

  fn signature_has_free_type_param(
    &self,
    sig: crate::SignatureId,
    bound: &mut Vec<TypeParamId>,
    visited: &mut AHashSet<TypeId>,
    depth: usize,
  ) -> bool {
    let sig = self.store.signature(sig);
    let bound_len = bound.len();
    bound.extend(sig.type_params.iter().map(|tp| tp.id));

    let result = sig.type_params.into_iter().any(|tp| {
      tp.constraint
        .map(|c| self.has_free_type_param(c, bound, visited, depth + 1))
        .unwrap_or(false)
        || tp
          .default
          .map(|d| self.has_free_type_param(d, bound, visited, depth + 1))
          .unwrap_or(false)
    }) || sig
      .params
      .into_iter()
      .any(|param| self.has_free_type_param(param.ty, bound, visited, depth + 1))
      || self.has_free_type_param(sig.ret, bound, visited, depth + 1)
      || sig
        .this_param
        .map(|this| self.has_free_type_param(this, bound, visited, depth + 1))
        .unwrap_or(false);

    bound.truncate(bound_len);
    result
  }

  pub fn new(store: Arc<TypeStore>, expander: &'a E) -> Self {
    Self::with_caches(
      store,
      expander,
      EvaluatorCaches::new(CacheConfig::default()),
    )
  }

  pub fn with_cache_config(store: Arc<TypeStore>, expander: &'a E, config: CacheConfig) -> Self {
    Self::with_caches(store, expander, EvaluatorCaches::new(config))
  }

  pub fn with_caches(store: Arc<TypeStore>, expander: &'a E, caches: EvaluatorCaches) -> Self {
    Self {
      store,
      expander,
      conditional_assignability: None,
      default_conditional_assignability: None,
      caches,
      eval_in_progress: AHashSet::new(),
      ref_in_progress: AHashSet::new(),
      subst_memo: std::collections::HashMap::new(),
      limits: EvaluatorLimits::default(),
      steps: 0,
      should_stop: None,
      budget_exceeded: false,
    }
  }

  pub(crate) fn with_conditional_assignability(
    mut self,
    provider: &'a dyn ConditionalAssignability,
  ) -> Self {
    self.conditional_assignability = Some(provider);
    self
  }

  pub fn with_limits(mut self, limits: EvaluatorLimits) -> Self {
    self.limits = limits;
    self
  }

  pub fn limits(&self) -> EvaluatorLimits {
    self.limits
  }

  pub fn with_depth_limit(mut self, limit: usize) -> Self {
    self.limits.depth_limit = limit;
    self
  }

  pub fn with_step_limit(mut self, limit: usize) -> Self {
    self.limits.step_limit = limit;
    self
  }

  pub fn with_max_template_strings(mut self, limit: usize) -> Self {
    self.limits.max_template_strings = limit;
    self
  }

  /// Install a cooperative stop flag (e.g. host cancellation). On stop the
  /// evaluator returns the input type unchanged and latches [`budget_exceeded`].
  pub fn with_should_stop(mut self, should_stop: &'a std::sync::atomic::AtomicBool) -> Self {
    self.should_stop = Some(should_stop);
    self
  }

  pub fn step_count(&self) -> usize {
    self.steps
  }

  pub fn budget_exceeded(&self) -> bool {
    self.budget_exceeded
  }

  pub fn cache_stats(&self) -> EvaluatorCacheStats {
    self.caches.stats()
  }

  pub fn clear_caches(&self) {
    self.caches.clear();
  }

  pub fn evaluate(&mut self, ty: TypeId) -> TypeId {
    self.steps = 0;
    #[cfg(feature = "tracing")]
    {
      let before_stats = self.caches.stats();
      let span = tracing::info_span!(
        "types_ts_interned::TypeEvaluator::evaluate",
        ty = ?ty,
        step_limit = self.limits.step_limit as u64,
        depth_limit = self.limits.depth_limit as u64,
        max_template_strings = self.limits.max_template_strings as u64,
        steps = tracing::field::Empty,
        eval_cache_hits = tracing::field::Empty,
        eval_cache_misses = tracing::field::Empty,
        ref_cache_hits = tracing::field::Empty,
        ref_cache_misses = tracing::field::Empty,
      );
      let _enter = span.enter();
      let result = self.evaluate_with_subst(ty, &Substitution::empty(), 0);
      let after_stats = self.caches.stats();
      let eval_delta = cache_stats_delta(before_stats.eval, after_stats.eval);
      let refs_delta = cache_stats_delta(before_stats.references, after_stats.references);
      span.record("steps", &(self.steps as u64));
      span.record("eval_cache_hits", &eval_delta.hits);
      span.record("eval_cache_misses", &eval_delta.misses);
      span.record("ref_cache_hits", &refs_delta.hits);
      span.record("ref_cache_misses", &refs_delta.misses);
      result
    }

    #[cfg(not(feature = "tracing"))]
    self.evaluate_with_subst(ty, &Substitution::empty(), 0)
  }

  pub fn evaluate_with_bindings<I>(&mut self, ty: TypeId, bindings: I) -> TypeId
  where
    I: IntoIterator<Item = (TypeParamId, TypeId)>,
  {
    let mut pairs: Vec<(TypeParamId, TypeId)> = bindings.into_iter().collect();
    pairs.sort_by_key(|(param, _)| param.0);
    pairs.dedup_by_key(|(param, _)| param.0);
    let subst = Substitution { bindings: pairs };
    self.steps = 0;
    self.evaluate_with_subst(ty, &subst, 0)
  }

  fn evaluate_with_subst(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    if depth >= self.limits.depth_limit {
      return ty;
    }
    if self
      .should_stop
      .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
    {
      self.budget_exceeded = true;
      return ty;
    }
    let key = EvalKey {
      gen: self.caches.generation.load(AtomicOrdering::Relaxed),
      ty,
      subst: subst.clone(),
    };
    if let Some(cached) = self.caches.eval.get(&key) {
      return cached;
    }

    if self.limits.step_limit != EvaluatorLimits::UNLIMITED_STEP_LIMIT {
      if self.steps >= self.limits.step_limit {
        self.budget_exceeded = true;
        return ty;
      }
      self.steps += 1;
    }

    if self.eval_in_progress.contains(&key) {
      return ty;
    }
    self.eval_in_progress.insert(key.clone());
    let result = match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => match subst.get(id) {
        Some(mapped) => self.evaluate_with_subst(mapped, subst, depth + 1),
        None => ty,
      },
      TypeKind::Infer { param, constraint } => match subst.get(param) {
        Some(mapped) => self.evaluate_with_subst(mapped, subst, depth + 1),
        None => {
          let constraint = constraint.map(|c| self.evaluate_with_subst(c, subst, depth + 1));
          self
            .store
            .intern_type(TypeKind::Infer { param, constraint })
        }
      },
      TypeKind::Union(members) => {
        let evaluated: Vec<_> = members
          .into_iter()
          .map(|m| self.evaluate_with_subst(m, subst, depth + 1))
          .collect();
        self.store.union(evaluated)
      }
      TypeKind::Intersection(members) => {
        let evaluated: Vec<_> = members
          .into_iter()
          .map(|m| self.evaluate_with_subst(m, subst, depth + 1))
          .collect();
        self.store.intersection(evaluated)
      }
      TypeKind::Array { ty, readonly } => {
        let elem = self.evaluate_with_subst(ty, subst, depth + 1);
        self
          .store
          .intern_type(TypeKind::Array { ty: elem, readonly })
      }
      TypeKind::Tuple(elems) => {
        let evaluated = elems
          .into_iter()
          .map(|elem| crate::TupleElem {
            ty: self.evaluate_with_subst(elem.ty, subst, depth + 1),
            optional: elem.optional,
            rest: elem.rest,
            readonly: elem.readonly,
          })
          .collect();
        self.store.intern_type(TypeKind::Tuple(evaluated))
      }
      TypeKind::Object(obj) => {
        // Empty subst + no reducible operators: identity (avoids re-interning
        // already-canonical structural graphs).
        if subst.bindings.is_empty() && !self.type_needs_evaluation(ty, 0) {
          ty
        } else {
          self.evaluate_object(obj, subst, depth + 1)
        }
      }
      TypeKind::Callable { overloads } => {
        if subst.bindings.is_empty() && !self.type_needs_evaluation(ty, 0) {
          ty
        } else {
          // Keep full signature evaluation for callables (lib method
          // instantiation / Promise.resolve assignability depends on it).
          // Nested object graphs inside parameter/return types are still
          // bounded via `evaluate_object`'s empty-subst `evaluate_ops` path.
          let overloads: Vec<_> = overloads
            .into_iter()
            .map(|sig| self.evaluate_signature(sig, subst, depth + 1))
            .collect();
          self.store.intern_type(TypeKind::Callable { overloads })
        }
      }
      TypeKind::Ref { def, args } => self.evaluate_ref(def, args, subst, depth + 1),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => self.evaluate_conditional(
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
        subst,
        depth + 1,
      ),
      TypeKind::Mapped(mapped) => self.evaluate_mapped(mapped, subst, depth + 1),
      TypeKind::TemplateLiteral(tpl) => self.evaluate_template_literal(tpl, subst, depth + 1),
      TypeKind::Intrinsic { kind, ty } => self.evaluate_intrinsic(kind, ty, subst, depth + 1),
      TypeKind::IndexedAccess { obj, index } => {
        self.evaluate_indexed_access(obj, index, subst, depth + 1)
      }
      TypeKind::KeyOf(inner) => self.evaluate_keyof(inner, subst, depth + 1),
      other => self.store.intern_type(other),
    };
    self.eval_in_progress.remove(&key);
    // Never cache a budget/cancel short-circuit: the result depends on remaining
    // steps in the caller, not solely on `(ty, subst)`, and would race under
    // shared evaluator caches.
    if !self.budget_exceeded {
      self.caches.eval.insert(key, result);
    }
    result
  }

  fn evaluate_signature(
    &mut self,
    sig: crate::SignatureId,
    subst: &Substitution,
    depth: usize,
  ) -> crate::SignatureId {
    let mut sig = self.store.signature(sig);
    sig.params.iter_mut().for_each(|param| {
      param.ty = self.evaluate_signature_type(param.ty, subst, depth + 1);
    });
    sig.ret = self.evaluate_signature_type(sig.ret, subst, depth + 1);
    if let Some(this) = sig.this_param.as_mut() {
      *this = self.evaluate_signature_type(*this, subst, depth + 1);
    }
    self.store.intern_signature(sig)
  }

  /// Evaluate a type that appears in a call/construct signature position.
  ///
  /// Under an empty subst, named `Ref`s (e.g. lib `Array<T>`) are left
  /// unexpanded: expanding them re-interns method graphs on every normalize
  /// pass and breaks Callable assignability (engine budget / false
  /// `SKIP_NORMALIZE` failures on `assignmentCompatWithCallSignatures3`).
  /// Concrete substitutions still fully evaluate so instantiation stays
  /// correct.
  fn evaluate_signature_type(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    if !subst.bindings.is_empty() {
      return self.evaluate_with_subst(ty, subst, depth);
    }
    if depth >= self.limits.depth_limit || self.budget_exceeded {
      return ty;
    }
    match self.store.type_kind(ty) {
      TypeKind::Ref { def, args } => {
        let args = args
          .into_iter()
          .map(|a| self.evaluate_signature_type(a, subst, depth + 1))
          .collect();
        self.store.intern_type(TypeKind::Ref { def, args })
      }
      TypeKind::Union(members) => {
        let members = members
          .into_iter()
          .map(|m| self.evaluate_signature_type(m, subst, depth + 1))
          .collect();
        self.store.union(members)
      }
      TypeKind::Intersection(members) => {
        let members = members
          .into_iter()
          .map(|m| self.evaluate_signature_type(m, subst, depth + 1))
          .collect();
        self.store.intersection(members)
      }
      TypeKind::Array { ty: elem, readonly } => {
        let elem = self.evaluate_signature_type(elem, subst, depth + 1);
        self
          .store
          .intern_type(TypeKind::Array { ty: elem, readonly })
      }
      TypeKind::Tuple(elems) => {
        let elems = elems
          .into_iter()
          .map(|mut e| {
            e.ty = self.evaluate_signature_type(e.ty, subst, depth + 1);
            e
          })
          .collect();
        self.store.intern_type(TypeKind::Tuple(elems))
      }
      TypeKind::Object(_) | TypeKind::Callable { .. } => ty,
      TypeKind::Conditional { .. }
      | TypeKind::Mapped(_)
      | TypeKind::TemplateLiteral(_)
      | TypeKind::Intrinsic { .. }
      | TypeKind::IndexedAccess { .. }
      | TypeKind::KeyOf(_)
      | TypeKind::Infer { .. } => self.evaluate_ops(ty, subst, depth),
      _ => ty,
    }
  }

  /// True if `ty` (or a shallow component) still contains a reducible operator
  /// that `evaluate_with_subst` must process. Used to skip identity object walks.
  fn type_needs_evaluation(&self, ty: TypeId, depth: usize) -> bool {
    if depth > 6 {
      // Bounded scan — prefer a false positive (extra eval) over deep walks.
      return true;
    }
    match self.store.type_kind(ty) {
      // Free type parameters are already normal under an empty subst (the only
      // caller of this helper). Forcing `true` here made every generic method
      // object look "reducible" and re-enabled deep `evaluate_object` walks.
      TypeKind::TypeParam(_) => false,
      TypeKind::Infer { .. }
      | TypeKind::Ref { .. }
      | TypeKind::Conditional { .. }
      | TypeKind::Mapped(_)
      | TypeKind::TemplateLiteral(_)
      | TypeKind::Intrinsic { .. }
      | TypeKind::IndexedAccess { .. }
      | TypeKind::KeyOf(_) => true,
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .iter()
        .any(|m| self.type_needs_evaluation(*m, depth + 1)),
      TypeKind::Array { ty, .. } => self.type_needs_evaluation(ty, depth + 1),
      TypeKind::Tuple(elems) => elems
        .iter()
        .any(|e| self.type_needs_evaluation(e.ty, depth + 1)),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        shape
          .properties
          .iter()
          .any(|p| self.type_needs_evaluation(p.data.ty, depth + 1))
          || shape.indexers.iter().any(|i| {
            self.type_needs_evaluation(i.key_type, depth + 1)
              || self.type_needs_evaluation(i.value_type, depth + 1)
          })
          || shape
            .call_signatures
            .iter()
            .chain(shape.construct_signatures.iter())
            .any(|sig| self.signature_needs_evaluation(*sig, depth + 1))
      }
      TypeKind::Callable { overloads } => overloads
        .iter()
        .any(|sig| self.signature_needs_evaluation(*sig, depth + 1)),
      _ => false,
    }
  }

  fn signature_needs_evaluation(&self, sig: crate::SignatureId, depth: usize) -> bool {
    let sig = self.store.signature(sig);
    // Signature positions leave named `Ref`s opaque under empty subst (see
    // `evaluate_signature_type`), so a free `Array<T>` in a parameter must not
    // force a full signature re-evaluation during Callable normalize.
    sig
      .params
      .iter()
      .any(|p| self.signature_type_needs_ops(p.ty, depth))
      || self.signature_type_needs_ops(sig.ret, depth)
      || sig
        .this_param
        .is_some_and(|t| self.signature_type_needs_ops(t, depth))
  }

  fn signature_type_needs_ops(&self, ty: TypeId, depth: usize) -> bool {
    if depth > 6 {
      return true;
    }
    match self.store.type_kind(ty) {
      TypeKind::Infer { .. }
      | TypeKind::Conditional { .. }
      | TypeKind::Mapped(_)
      | TypeKind::TemplateLiteral(_)
      | TypeKind::Intrinsic { .. }
      | TypeKind::IndexedAccess { .. }
      | TypeKind::KeyOf(_) => true,
      TypeKind::Ref { args, .. } => args
        .iter()
        .any(|a| self.signature_type_needs_ops(*a, depth + 1)),
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .iter()
        .any(|m| self.signature_type_needs_ops(*m, depth + 1)),
      TypeKind::Array { ty, .. } => self.signature_type_needs_ops(ty, depth + 1),
      TypeKind::Tuple(elems) => elems
        .iter()
        .any(|e| self.signature_type_needs_ops(e.ty, depth + 1)),
      _ => false,
    }
  }

  /// Evaluate reducible operators under `subst`, but treat nested `Object` /
  /// `Callable` as opaque when `subst` is empty. This is a pure function of
  /// `(ty, subst)` (unlike depth-dependent early exits) and prevents
  /// signature↔object recursion from allocating unbounded shapes.
  fn evaluate_ops(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    if depth >= self.limits.depth_limit || self.budget_exceeded {
      return ty;
    }
    if self
      .should_stop
      .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
    {
      self.budget_exceeded = true;
      return ty;
    }
    if self.limits.step_limit != EvaluatorLimits::UNLIMITED_STEP_LIMIT {
      if self.steps >= self.limits.step_limit {
        self.budget_exceeded = true;
        return ty;
      }
      self.steps += 1;
    }
    match self.store.type_kind(ty) {
      TypeKind::Object(_) if subst.bindings.is_empty() => ty,
      TypeKind::TypeParam(id) => subst
        .get(id)
        .map(|mapped| self.evaluate_ops(mapped, subst, depth + 1))
        .unwrap_or(ty),
      TypeKind::Union(members) => {
        let evaluated: Vec<_> = members
          .into_iter()
          .map(|m| self.evaluate_ops(m, subst, depth + 1))
          .collect();
        self.store.union(evaluated)
      }
      TypeKind::Intersection(members) => {
        let evaluated: Vec<_> = members
          .into_iter()
          .map(|m| self.evaluate_ops(m, subst, depth + 1))
          .collect();
        self.store.intersection(evaluated)
      }
      TypeKind::Array { ty: elem, readonly } => {
        let elem = self.evaluate_ops(elem, subst, depth + 1);
        self
          .store
          .intern_type(TypeKind::Array { ty: elem, readonly })
      }
      TypeKind::Tuple(elems) => {
        let evaluated = elems
          .into_iter()
          .map(|elem| crate::TupleElem {
            ty: self.evaluate_ops(elem.ty, subst, depth + 1),
            optional: elem.optional,
            rest: elem.rest,
            readonly: elem.readonly,
          })
          .collect();
        self.store.intern_type(TypeKind::Tuple(evaluated))
      }
      TypeKind::Ref { def, args } => self.evaluate_ref(def, args, subst, depth + 1),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => self.evaluate_conditional(
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
        subst,
        depth + 1,
      ),
      TypeKind::Mapped(mapped) => self.evaluate_mapped(mapped, subst, depth + 1),
      TypeKind::TemplateLiteral(tpl) => self.evaluate_template_literal(tpl, subst, depth + 1),
      TypeKind::Intrinsic { kind, ty } => self.evaluate_intrinsic(kind, ty, subst, depth + 1),
      TypeKind::IndexedAccess { obj, index } => {
        self.evaluate_indexed_access(obj, index, subst, depth + 1)
      }
      TypeKind::KeyOf(inner) => self.evaluate_keyof(inner, subst, depth + 1),
      TypeKind::Infer { param, constraint } => match subst.get(param) {
        Some(mapped) => self.evaluate_ops(mapped, subst, depth + 1),
        None => {
          let constraint = constraint.map(|c| self.evaluate_ops(c, subst, depth + 1));
          self
            .store
            .intern_type(TypeKind::Infer { param, constraint })
        }
      },
      // Non-empty subst must still walk objects for substitution.
      TypeKind::Object(obj) => self.evaluate_object(obj, subst, depth + 1),
      TypeKind::Callable { overloads } => {
        let overloads: Vec<_> = overloads
          .into_iter()
          .map(|sig| {
            if subst.bindings.is_empty() {
              self.evaluate_signature_ops(sig, subst, depth + 1)
            } else {
              self.evaluate_signature(sig, subst, depth + 1)
            }
          })
          .collect();
        self.store.intern_type(TypeKind::Callable { overloads })
      }
      other => self.store.intern_type(other),
    }
  }

  /// Evaluate only call/construct signatures on an object; leave properties
  /// untouched. Used when a nested object appears under an empty subst.
  fn evaluate_object_signatures_only(
    &mut self,
    obj: ObjectId,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    if depth >= self.limits.depth_limit || self.budget_exceeded {
      return self.store.intern_type(TypeKind::Object(obj));
    }
    let object = self.store.object(obj);
    let mut shape = self.store.shape(object.shape);
    if shape.call_signatures.is_empty() && shape.construct_signatures.is_empty() {
      return self.store.intern_type(TypeKind::Object(obj));
    }
    shape.call_signatures = shape
      .call_signatures
      .into_iter()
      .map(|sig| self.evaluate_signature_ops(sig, subst, depth + 1))
      .collect();
    shape.construct_signatures = shape
      .construct_signatures
      .into_iter()
      .map(|sig| self.evaluate_signature_ops(sig, subst, depth + 1))
      .collect();
    if self.budget_exceeded {
      return self.store.intern_type(TypeKind::Object(obj));
    }
    let shape_id = self.store.intern_shape(shape);
    let obj_id = self
      .store
      .intern_object(crate::ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj_id))
  }

  fn evaluate_signature_ops(
    &mut self,
    sig: crate::SignatureId,
    subst: &Substitution,
    depth: usize,
  ) -> crate::SignatureId {
    let mut sig = self.store.signature(sig);
    sig.params.iter_mut().for_each(|param| {
      param.ty = self.evaluate_signature_type(param.ty, subst, depth + 1);
    });
    sig.ret = self.evaluate_signature_type(sig.ret, subst, depth + 1);
    if let Some(this) = sig.this_param.as_mut() {
      *this = self.evaluate_signature_type(*this, subst, depth + 1);
    }
    self.store.intern_signature(sig)
  }

  fn evaluate_object(&mut self, obj: ObjectId, subst: &Substitution, depth: usize) -> TypeId {
    if self.budget_exceeded
      || self
        .should_stop
        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
    {
      self.budget_exceeded = true;
      return self.store.intern_type(TypeKind::Object(obj));
    }
    let object = self.store.object(obj);
    let mut shape = self.store.shape(object.shape);
    // A subst that only renames type parameters (or is empty) must not deep-walk
    // nested object property graphs — `evaluate_ref` often builds such substs
    // when expanding `Promise<T>`-like refs, and re-entering `evaluate_object`
    // there is the `parserRealSource12` memory bomb. Concrete substitutions
    // (T → number, …) still walk fully so instantiation stays correct.
    let deep_object_walk = subst
      .bindings
      .iter()
      .any(|(_, ty)| !matches!(self.store.type_kind(*ty), TypeKind::TypeParam(_)));
    for prop in shape.properties.iter_mut() {
      prop.data.ty = if !deep_object_walk {
        match self.store.type_kind(prop.data.ty) {
          TypeKind::Object(inner) => self.evaluate_object_signatures_only(inner, subst, depth + 1),
          _ => self.evaluate_with_subst(prop.data.ty, subst, depth + 1),
        }
      } else {
        self.evaluate_with_subst(prop.data.ty, subst, depth + 1)
      };
      if self.budget_exceeded {
        return self.store.intern_type(TypeKind::Object(obj));
      }
    }
    for idx in shape.indexers.iter_mut() {
      if !deep_object_walk {
        if !matches!(self.store.type_kind(idx.key_type), TypeKind::Object(_)) {
          idx.key_type = self.evaluate_with_subst(idx.key_type, subst, depth + 1);
        }
        if !matches!(self.store.type_kind(idx.value_type), TypeKind::Object(_)) {
          idx.value_type = self.evaluate_with_subst(idx.value_type, subst, depth + 1);
        }
      } else {
        idx.key_type = self.evaluate_with_subst(idx.key_type, subst, depth + 1);
        idx.value_type = self.evaluate_with_subst(idx.value_type, subst, depth + 1);
      }
      if self.budget_exceeded {
        return self.store.intern_type(TypeKind::Object(obj));
      }
    }
    shape.call_signatures = shape
      .call_signatures
      .into_iter()
      .map(|sig| {
        if deep_object_walk {
          self.evaluate_signature(sig, subst, depth + 1)
        } else {
          self.evaluate_signature_ops(sig, subst, depth + 1)
        }
      })
      .collect();
    if self.budget_exceeded {
      return self.store.intern_type(TypeKind::Object(obj));
    }
    shape.construct_signatures = shape
      .construct_signatures
      .into_iter()
      .map(|sig| {
        if deep_object_walk {
          self.evaluate_signature(sig, subst, depth + 1)
        } else {
          self.evaluate_signature_ops(sig, subst, depth + 1)
        }
      })
      .collect();
    if self.budget_exceeded {
      return self.store.intern_type(TypeKind::Object(obj));
    }
    let shape_id = self.store.intern_shape(shape);
    let obj_id = self
      .store
      .intern_object(crate::ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj_id))
  }

  /// Structural substitution without evaluation: replaces bound type
  /// parameters via `subst` and rebuilds composite nodes, but never expands
  /// `Ref`s (their args are rebuilt structurally instead). Used by the
  /// recursive-generic deferral in [`TypeEvaluator::evaluate_ref`], where
  /// the deferred reference must carry substituted args without triggering
  /// further expansion.
  fn substitute_only(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    if depth >= self.limits.depth_limit {
      return ty;
    }
    // DAG sharing memo: valid only for the current `evaluate_ref` invocation's
    // substitution (the caller scopes `subst_memo` to that window).
    if let Some(memo) = self.subst_memo.get(&ty) {
      return *memo;
    }
    let result = match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => subst.get(id).unwrap_or(ty),
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.substitute_only(m, subst, depth + 1))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.substitute_only(m, subst, depth + 1))
          .collect();
        self.store.intersection(mapped)
      }
      TypeKind::Array { ty, readonly } => {
        let inner = self.substitute_only(ty, subst, depth + 1);
        self.store.intern_type(TypeKind::Array {
          ty: inner,
          readonly,
        })
      }
      TypeKind::Tuple(elems) => {
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| crate::TupleElem {
            ty: self.substitute_only(elem.ty, subst, depth + 1),
            optional: elem.optional,
            rest: elem.rest,
            readonly: elem.readonly,
          })
          .collect();
        self.store.intern_type(TypeKind::Tuple(mapped))
      }
      TypeKind::KeyOf(inner) => {
        let inner = self.substitute_only(inner, subst, depth + 1);
        self.store.intern_type(TypeKind::KeyOf(inner))
      }
      TypeKind::IndexedAccess { obj, index } => {
        let obj = self.substitute_only(obj, subst, depth + 1);
        let index = self.substitute_only(index, subst, depth + 1);
        self
          .store
          .intern_type(TypeKind::IndexedAccess { obj, index })
      }
      TypeKind::Intrinsic { kind, ty } => {
        let ty = self.substitute_only(ty, subst, depth + 1);
        self.store.intern_type(TypeKind::Intrinsic { kind, ty })
      }
      TypeKind::Ref { def, args } => {
        let mapped: Vec<TypeId> = args
          .into_iter()
          .map(|arg| self.substitute_only(arg, subst, depth + 1))
          .collect();
        self.store.intern_type(TypeKind::Ref { def, args: mapped })
      }
      // Objects, callables, operators, and primitives: shapes here do not
      // carry the in-flight subst's free parameters (they belong to the
      // already-instantiated definition), so return as-is.
      _ => ty,
    };
    self.subst_memo.insert(ty, result);
    result
  }

  fn evaluate_ref(
    &mut self,
    def: DefId,
    args: Vec<TypeId>,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    // Args are substituted structurally (no eager expansion): expanding Ref
    // arguments here eagerly is what makes recursive generics with growing
    // args quadratic (`new D<string>()` on `class D<T> { wrapped: D<D<T>> }`
    // — each nesting level re-expanded the full chain below it). tsc keeps
    // type arguments as references; downstream evaluation expands lazily on
    // demand. `substitute_only` applies the in-flight substitution without
    // evaluating.
    //
    // The memo is scoped to this invocation's substitution: nested
    // `evaluate_ref` calls extend the substitution, so they save/restore.
    let saved_subst_memo = std::mem::take(&mut self.subst_memo);
    let evaluated_args: SmallVec<[TypeId; 4]> = args
      .into_iter()
      .map(|arg| self.substitute_only(arg, subst, 0))
      .collect();
    self.subst_memo = saved_subst_memo;
    let key = RefKey {
      gen: self.caches.generation.load(AtomicOrdering::Relaxed),
      def,
      args: evaluated_args,
    };
    if let Some(cached) = self.caches.refs.get(&key) {
      // `refs` memoizes instantiated expansions, but callers may evolve the
      // underlying definition tables over time (e.g. lazy type loading in a
      // query-based program) or populate ref caches from partially-expanded
      // contexts (such as relation checks that only expand through a `Ref`
      // boundary). In that situation a cached expansion might still contain
      // operators that are now reducible (e.g. `Uppercase<"a">` -> `"A"`).
      //
      // Re-evaluate cached reference results once to avoid permanently
      // "sticking" to a partially-expanded ref chain.
      if matches!(
        self.store.type_kind(cached),
        TypeKind::Ref { .. } | TypeKind::Intrinsic { .. }
      ) {
        let evaluated = self.evaluate_with_subst(cached, subst, depth + 1);
        if evaluated != cached {
          self.caches.refs.insert(key, evaluated);
          return evaluated;
        }
      }
      return cached;
    }
    if self.ref_in_progress.contains(&key) {
      return self.store.intern_type(TypeKind::Ref {
        def,
        args: key.args.to_vec(),
      });
    }
    self.ref_in_progress.insert(key.clone());
    // When the expander declines (e.g. SkipSelfExpander leaving nested
    // `C<U>` as a ref while instantiating `C<T>`), the synthesized Ref is a
    // *deferred* expansion — not a final answer. Caching it poisons later
    // `expand_ref(C, [U])` via the shared `EvaluatorCaches` (dual generic
    // class instantiations → false TS2339 / one-way assignability).
    let (expanded, cacheable) = match self.expander.expand(&self.store, def, &key.args) {
      Some(expanded) => {
        let mut next_subst = subst.clone();
        for (idx, param) in expanded.params.iter().enumerate() {
          if let Some(arg) = key.args.get(idx) {
            next_subst = next_subst.with(*param, *arg);
          }
        }
        (
          self.evaluate_with_subst(expanded.ty, &next_subst, depth + 1),
          true,
        )
      }
      None => (
        self.store.intern_type(TypeKind::Ref {
          def,
          args: key.args.to_vec(),
        }),
        false,
      ),
    };
    self.ref_in_progress.remove(&key);
    if cacheable {
      self.caches.refs.insert(key, expanded);
    }
    expanded
  }

  fn evaluate_conditional(
    &mut self,
    check: TypeId,
    extends: TypeId,
    true_ty: TypeId,
    false_ty: TypeId,
    distributive: bool,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    #[cfg(feature = "tracing")]
    let span = tracing::debug_span!(
      "types_ts_interned::TypeEvaluator::evaluate_conditional",
      check = ?check,
      extends = ?extends,
      distributive,
      indeterminate = tracing::field::Empty,
      deferred = tracing::field::Empty,
      assignable = tracing::field::Empty,
      result = tracing::field::Empty,
    );
    #[cfg(feature = "tracing")]
    let _enter = span.enter();

    let raw_check_param = match self.store.type_kind(check) {
      TypeKind::TypeParam(param) => Some(param),
      _ => None,
    };
    let check_eval = self.evaluate_with_subst(check, subst, depth + 1);
    // TypeScript conditional types have a few special cases that are not
    // captured by simple assignability checks:
    //
    // - Distributive conditional types instantiated with `never` evaluate to
    //   `never` (distribution over an empty union).
    // - `any` is treated as both assignable and not-assignable, producing the
    //   union of both branches.
    //
    // Note: distribution must occur before any deferral logic (returning an
    // unevaluated conditional) so that `extends` is evaluated with the per-union
    // member substitution (e.g. `T -> member`) rather than once with the full
    // union binding.
    match self.store.type_kind(check_eval) {
      TypeKind::Never if distributive => {
        let result = self.store.primitive_ids().never;
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        return result;
      }
      TypeKind::Any => {
        let true_eval = self.evaluate_with_subst(true_ty, subst, depth + 1);
        let false_eval = self.evaluate_with_subst(false_ty, subst, depth + 1);
        let result = self.store.union(vec![true_eval, false_eval]);
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        return result;
      }
      TypeKind::Union(members) if distributive => {
        let mut results = Vec::new();
        for member in members {
          let member_distributive = matches!(self.store.type_kind(member), TypeKind::TypeParam(_));
          let mut inner_subst = subst.clone();
          if let Some(param) = raw_check_param {
            inner_subst = inner_subst.with(param, member);
          }
          results.push(self.evaluate_conditional(
            member,
            extends,
            true_ty,
            false_ty,
            member_distributive,
            &inner_subst,
            depth + 1,
          ));
        }
        let result = self.store.union(results);
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        return result;
      }
      _ => {}
    }

    let extends_eval = self.evaluate_with_subst(extends, subst, depth + 1);

    // Conditional types are only reducible once their operands are known.
    //
    // When the assignability check depends on free (unsubstituted) type
    // parameters we must defer evaluation instead of incorrectly picking a
    // branch.
    let mut bound = Vec::new();
    let mut visited = AHashSet::new();
    let indeterminate = self.has_free_type_param(check_eval, &mut bound, &mut visited, 0)
      || self.has_free_type_param(extends_eval, &mut bound, &mut visited, 0)
      || self.conditional_is_indeterminate_operand(check_eval, subst, depth + 1)
      || self.conditional_is_indeterminate_operand(extends_eval, subst, depth + 1);
    if indeterminate {
      #[cfg(feature = "tracing")]
      {
        span.record("indeterminate", &true);
      }
      // Some conditional types include `infer` placeholders in the `extends`
      // operand (e.g. `Awaited<T>`, `ReturnType<T>`). We cannot generally reduce
      // these without performing inference, but we *can* still pick the false
      // branch when the `check` type is provably incompatible with a concrete
      // (non-`infer`) part of the `extends` type.
      //
      // This is important for upstream lib declarations like
      // `Promise.resolve<T>(value: T): Promise<Awaited<T>>`, where
      // `Awaited<"ok">` should reduce to `"ok"` even though `Awaited` is written
      // in terms of `infer`.
      if self.conditional_definitely_not_assignable(check_eval, extends_eval, depth + 1) {
        #[cfg(feature = "tracing")]
        {
          span.record("deferred", &false);
        }
        let result = self.evaluate_with_subst(false_ty, subst, depth + 1);
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        return result;
      }

      let true_eval = self.evaluate_with_subst(true_ty, subst, depth + 1);
      let false_eval = self.evaluate_with_subst(false_ty, subst, depth + 1);
      let result = self.store.intern_type(TypeKind::Conditional {
        check: check_eval,
        extends: extends_eval,
        true_ty: true_eval,
        false_ty: false_eval,
        distributive,
      });
      #[cfg(feature = "tracing")]
      {
        span.record("deferred", &true);
        span.record("result", &tracing::field::debug(&result));
      }
      return result;
    }

    let assignable = match self.conditional_assignability {
      Some(provider) => provider.is_assignable_for_conditional(check_eval, extends_eval),
      None => {
        if self.default_conditional_assignability.is_none() {
          self.default_conditional_assignability =
            Some(RelateCtx::new(self.store.clone(), self.store.options()));
        }
        self
          .default_conditional_assignability
          .as_ref()
          .expect("default conditional assignability must be initialized")
          .is_assignable_for_conditional(check_eval, extends_eval)
      }
    };
    #[cfg(feature = "tracing")]
    {
      span.record("assignable", &assignable);
    }

    let branch = if assignable { true_ty } else { false_ty };
    let result = self.evaluate_with_subst(branch, subst, depth + 1);
    #[cfg(feature = "tracing")]
    {
      span.record("result", &tracing::field::debug(&result));
    }
    result
  }

  /// Conservative fast path for conditional-type reduction in the presence of
  /// indeterminate operands (notably `infer` placeholders).
  ///
  /// Returns `true` only when `check` is *definitely* not assignable to
  /// `extends`, so that selecting the false branch is sound without performing
  /// inference.
  fn conditional_definitely_not_assignable(
    &self,
    check: TypeId,
    extends: TypeId,
    depth: usize,
  ) -> bool {
    if depth >= self.limits.depth_limit {
      return false;
    }

    let check_kind = self.store.type_kind(check);
    if !self.kind_definitely_non_object_like(&check_kind) {
      return false;
    }

    self.type_requires_object_like(extends, depth + 1)
  }

  fn kind_definitely_non_object_like(&self, kind: &TypeKind) -> bool {
    matches!(
      kind,
      TypeKind::Unknown
        | TypeKind::Void
        | TypeKind::Null
        | TypeKind::Undefined
        | TypeKind::Boolean
        | TypeKind::BooleanLiteral(_)
        | TypeKind::Number
        | TypeKind::NumberLiteral(_)
        | TypeKind::String
        | TypeKind::StringLiteral(_)
        | TypeKind::BigInt
        | TypeKind::BigIntLiteral(_)
        | TypeKind::Symbol
        | TypeKind::UniqueSymbol
    )
  }

  fn type_requires_object_like(&self, ty: TypeId, depth: usize) -> bool {
    if depth >= self.limits.depth_limit {
      return false;
    }
    match self.store.type_kind(ty) {
      TypeKind::Object(_) => true,
      TypeKind::Intersection(members) => members
        .into_iter()
        .any(|member| self.type_requires_object_like(member, depth + 1)),
      _ => false,
    }
  }

  fn conditional_is_indeterminate_operand(
    &self,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> bool {
    let mut visited = AHashSet::new();
    self.conditional_is_indeterminate_operand_inner(ty, subst, depth, &mut visited)
  }

  fn conditional_is_indeterminate_operand_inner(
    &self,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
    visited: &mut AHashSet<TypeId>,
  ) -> bool {
    if depth >= self.limits.depth_limit {
      // If we can't soundly inspect the operand (usually due to deep recursion),
      // do not attempt to reduce the conditional.
      return true;
    }
    if !visited.insert(ty) {
      return false;
    }

    match self.store.type_kind(ty) {
      TypeKind::Infer { .. } => true,
      // `TypeParam` occurrences are handled separately via `has_free_type_param`
      // so that we can respect binding scopes (signatures/mapped types) and
      // avoid false positives from locally-bound parameters.
      TypeKind::TypeParam(_) => false,
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .into_iter()
        .any(|m| self.conditional_is_indeterminate_operand_inner(m, subst, depth + 1, visited)),
      TypeKind::Array { ty, .. } => {
        self.conditional_is_indeterminate_operand_inner(ty, subst, depth + 1, visited)
      }
      TypeKind::Tuple(elems) => elems.into_iter().any(|elem| {
        self.conditional_is_indeterminate_operand_inner(elem.ty, subst, depth + 1, visited)
      }),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        shape.properties.iter().any(|prop| {
          self.conditional_is_indeterminate_operand_inner(prop.data.ty, subst, depth + 1, visited)
        }) || shape.indexers.iter().any(|idx| {
          self.conditional_is_indeterminate_operand_inner(idx.key_type, subst, depth + 1, visited)
            || self.conditional_is_indeterminate_operand_inner(
              idx.value_type,
              subst,
              depth + 1,
              visited,
            )
        }) || shape
          .call_signatures
          .iter()
          .any(|sig| self.conditional_signature_is_indeterminate(*sig, subst, depth + 1, visited))
          || shape
            .construct_signatures
            .iter()
            .any(|sig| self.conditional_signature_is_indeterminate(*sig, subst, depth + 1, visited))
      }
      TypeKind::Callable { overloads } => overloads
        .into_iter()
        .any(|sig| self.conditional_signature_is_indeterminate(sig, subst, depth + 1, visited)),
      TypeKind::Ref { .. } => true,
      TypeKind::Predicate { asserted, .. } => asserted.is_some_and(|asserted| {
        self.conditional_is_indeterminate_operand_inner(asserted, subst, depth + 1, visited)
      }),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        ..
      } => {
        self.conditional_is_indeterminate_operand_inner(check, subst, depth + 1, visited)
          || self.conditional_is_indeterminate_operand_inner(extends, subst, depth + 1, visited)
          || self.conditional_is_indeterminate_operand_inner(true_ty, subst, depth + 1, visited)
          || self.conditional_is_indeterminate_operand_inner(false_ty, subst, depth + 1, visited)
      }
      TypeKind::Mapped(mapped) => {
        self.conditional_is_indeterminate_operand_inner(mapped.source, subst, depth + 1, visited)
          || self.conditional_is_indeterminate_operand_inner(
            mapped.value,
            subst,
            depth + 1,
            visited,
          )
          || mapped.name_type.is_some_and(|ty| {
            self.conditional_is_indeterminate_operand_inner(ty, subst, depth + 1, visited)
          })
          || mapped.as_type.is_some_and(|ty| {
            self.conditional_is_indeterminate_operand_inner(ty, subst, depth + 1, visited)
          })
      }
      TypeKind::TemplateLiteral(tpl) => tpl.spans.into_iter().any(|chunk| {
        self.conditional_is_indeterminate_operand_inner(chunk.ty, subst, depth + 1, visited)
      }),
      TypeKind::IndexedAccess { obj, index } => {
        self.conditional_is_indeterminate_operand_inner(obj, subst, depth + 1, visited)
          || self.conditional_is_indeterminate_operand_inner(index, subst, depth + 1, visited)
      }
      TypeKind::KeyOf(inner) => {
        self.conditional_is_indeterminate_operand_inner(inner, subst, depth + 1, visited)
      }
      TypeKind::Intrinsic { .. } => true,
      _ => false,
    }
  }

  fn conditional_signature_is_indeterminate(
    &self,
    sig: crate::SignatureId,
    subst: &Substitution,
    depth: usize,
    visited: &mut AHashSet<TypeId>,
  ) -> bool {
    let sig = self.store.signature(sig);
    sig.params.iter().any(|param| {
      self.conditional_is_indeterminate_operand_inner(param.ty, subst, depth + 1, visited)
    }) || self.conditional_is_indeterminate_operand_inner(sig.ret, subst, depth + 1, visited)
      || sig.this_param.is_some_and(|this| {
        self.conditional_is_indeterminate_operand_inner(this, subst, depth + 1, visited)
      })
      || sig.type_params.iter().any(|tp| {
        tp.constraint.is_some_and(|constraint| {
          self.conditional_is_indeterminate_operand_inner(constraint, subst, depth + 1, visited)
        }) || tp.default.is_some_and(|default| {
          self.conditional_is_indeterminate_operand_inner(default, subst, depth + 1, visited)
        })
      })
  }

  fn evaluate_mapped(&mut self, mapped: MappedType, subst: &Substitution, depth: usize) -> TypeId {
    #[cfg(feature = "tracing")]
    let span = tracing::debug_span!(
      "types_ts_interned::TypeEvaluator::evaluate_mapped",
      source = ?mapped.source,
      value = ?mapped.value,
      entry_count = tracing::field::Empty,
      result = tracing::field::Empty,
    );
    #[cfg(feature = "tracing")]
    let _enter = span.enter();

    // tsc `instantiateConstituent`: for a *homomorphic* mapped type
    // `{[P in keyof T]: X}`, instantiating `T` with a non-object source
    // performs no mapping and yields the source itself
    // (`DeepReadonly<number>` is `number`); a union source distributes the
    // mapped type per member, primitives passing through
    // (`DeepReadonly<A | undefined>` is `DeepReadonly<A> | undefined`).
    if let Some(hom_var) = mapped.homomorphic_var {
      let TypeKind::KeyOf(hom_src) = self.store.type_kind(mapped.source) else {
        unreachable!("homomorphic_var is only set for keyof sources");
      };
      let src_eval = self.evaluate_with_subst(hom_src, subst, depth + 1);
      // tsc `instantiateConstituent`: mappable = `AnyOrUnknown` |
      // `InstantiableNonPrimitive` | `Object` | `Intersection` — everything
      // else (primitives, `never`, `void`, `null`, `undefined`) passes
      // through unmapped.
      fn is_mappable(store: &TypeStore, ty: TypeId) -> bool {
        matches!(
          store.type_kind(ty),
          TypeKind::Object(_)
            | TypeKind::Intersection(_)
            | TypeKind::Any
            | TypeKind::Unknown
            | TypeKind::TypeParam(_)
            | TypeKind::IndexedAccess { .. }
            | TypeKind::Conditional { .. }
            | TypeKind::Mapped(_)
        )
      }
      match self.store.type_kind(src_eval) {
        TypeKind::Union(members) => {
          let mut out = Vec::new();
          for member in members {
            if is_mappable(&self.store, member) {
              // Re-map with the homomorphic variable bound to this member
              // (tsc distributes the mapped type per union constituent). The
              // source is also replaced because eager substitution paths may
              // already have baked the union into it.
              let member_source = self.store.intern_type(TypeKind::KeyOf(member));
              let member_subst = subst.clone().with(hom_var, member);
              out.push(self.evaluate_mapped(
                MappedType {
                  source: member_source,
                  ..mapped.clone()
                },
                &member_subst,
                depth + 1,
              ));
            } else {
              out.push(member);
            }
          }
          let result = self.store.union(out);
          #[cfg(feature = "tracing")]
          {
            span.record("result", &tracing::field::debug(&result));
          }
          return result;
        }
        _ if !is_mappable(&self.store, src_eval) => {
          #[cfg(feature = "tracing")]
          {
            span.record("result", &tracing::field::debug(&src_eval));
          }
          return src_eval;
        }
        _ => {}
      }
    }

    let entries = self.mapped_entries(mapped.source, subst, depth + 1);
    #[cfg(feature = "tracing")]
    {
      span.record("entry_count", &(entries.len() as u64));
    }

    let mut properties = Vec::new();
    let mut indexers = Vec::new();
    for entry in entries {
      let key_tys = self.mapped_key_type_ids(&entry.key);
      let mut inner_subst = subst.clone();
      inner_subst = inner_subst.with(mapped.param, key_tys.original);
      let value_ty = self.evaluate_with_subst(mapped.value, &inner_subst, depth + 1);
      let readonly = match mapped.readonly {
        MappedModifier::Preserve => entry.readonly,
        MappedModifier::Add => true,
        MappedModifier::Remove => false,
      };
      let optional = match mapped.optional {
        MappedModifier::Preserve => entry.optional,
        MappedModifier::Add => true,
        MappedModifier::Remove => false,
      };

      let remap_keys = self.remap_mapped_key(&mapped, &entry.key, &inner_subst, depth + 1);
      let remap_keys = match remap_keys {
        KeySet::Unknown => KeySet::known(vec![Key::String, Key::Number, Key::Symbol], &self.store),
        other => other,
      };

      let KeySet::Known(keys) = remap_keys else {
        unreachable!("remap_keys should be normalized above");
      };
      if keys.is_empty() {
        continue;
      }

      let mut index_value_ty = value_ty;
      if optional {
        index_value_ty = self
          .store
          .union(vec![index_value_ty, self.store.primitive_ids().undefined]);
      }

      for key in keys {
        match key {
          Key::String => indexers.push(crate::Indexer {
            key_type: self.store.primitive_ids().string,
            value_type: index_value_ty,
            readonly,
          }),
          Key::Number => indexers.push(crate::Indexer {
            key_type: self.store.primitive_ids().number,
            value_type: index_value_ty,
            readonly,
          }),
          Key::Symbol => indexers.push(crate::Indexer {
            key_type: self.store.primitive_ids().symbol,
            value_type: index_value_ty,
            readonly,
          }),
          Key::Literal(prop_key) => properties.push(Property {
            key: prop_key,
            data: PropData {
              ty: value_ty,
              optional,
              readonly,
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          }),
        }
      }
    }

    let shape = Shape {
      properties,
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      indexers,
    };

    // Mapped types always produce an object type literal. If it has no keys, the
    // result is the empty object type literal `{}` (which is semantically
    // distinct from the `object` keyword).
    if shape.properties.is_empty()
      && shape.indexers.is_empty()
      && shape.call_signatures.is_empty()
      && shape.construct_signatures.is_empty()
    {
      let result = self.store.intern_type(TypeKind::EmptyObject);
      #[cfg(feature = "tracing")]
      {
        span.record("result", &tracing::field::debug(&result));
      }
      return result;
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self
      .store
      .intern_object(crate::ObjectType { shape: shape_id });
    let result = self.store.intern_type(TypeKind::Object(obj));
    #[cfg(feature = "tracing")]
    {
      span.record("result", &tracing::field::debug(&result));
    }
    result
  }

  fn remap_mapped_key(
    &mut self,
    mapped: &MappedType,
    entry: &Key,
    subst: &Substitution,
    depth: usize,
  ) -> KeySet {
    let remap_ty = mapped.as_type.or(mapped.name_type);
    let Some(remap_ty) = remap_ty else {
      return KeySet::known(vec![entry.clone()], &self.store);
    };
    let key_tys = self.mapped_key_type_ids(entry);
    let mut inner_subst = subst.clone();
    inner_subst = inner_subst.with(mapped.param, key_tys.original);
    let evaluated = self.evaluate_with_subst(remap_ty, &inner_subst, depth + 1);
    self.keys_from_index_type(evaluated)
  }

  fn mapped_key_type_ids(&self, key: &Key) -> MappedKeyTypes {
    let primitives = self.store.primitive_ids();
    match key {
      Key::Literal(PropKey::String(id)) => MappedKeyTypes {
        original: self.store.intern_type(TypeKind::StringLiteral(*id)),
      },
      Key::Literal(PropKey::Number(num)) => MappedKeyTypes {
        original: self
          .store
          .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(*num as f64))),
      },
      Key::Literal(PropKey::Symbol(_)) => MappedKeyTypes {
        original: primitives.symbol,
      },
      Key::String => MappedKeyTypes {
        original: primitives.string,
      },
      Key::Number => MappedKeyTypes {
        original: primitives.number,
      },
      Key::Symbol => MappedKeyTypes {
        original: primitives.symbol,
      },
    }
  }

  fn mapped_entries(&mut self, source: TypeId, subst: &Substitution, depth: usize) -> Vec<KeyInfo> {
    if let TypeKind::KeyOf(inner) = self.store.type_kind(source) {
      let evaluated_inner = self.evaluate_with_subst(inner, subst, depth + 1);
      return self.keys_from_type_as_entries(evaluated_inner, subst, depth + 1);
    }

    let evaluated_source = self.evaluate_with_subst(source, subst, depth + 1);
    match self.store.type_kind(evaluated_source) {
      TypeKind::Union(members) => {
        let mut entries = Vec::new();
        for member in members {
          entries.extend(self.keys_from_type_as_entries(member, subst, depth + 1));
        }
        self.dedup_entries(entries)
      }
      TypeKind::Intersection(members) => {
        let mut entries = Vec::new();
        for member in members {
          entries.extend(self.keys_from_type_as_entries(member, subst, depth + 1));
        }
        self.dedup_entries(entries)
      }
      other => self.keys_from_type_as_entries(self.store.intern_type(other), subst, depth + 1),
    }
  }

  fn dedup_entries(&self, entries: Vec<KeyInfo>) -> Vec<KeyInfo> {
    let mut merged: AHashMap<Key, (bool, bool)> = AHashMap::new();
    for entry in entries.into_iter() {
      merged
        .entry(entry.key)
        .and_modify(|existing| {
          existing.0 |= entry.optional;
          existing.1 |= entry.readonly;
        })
        .or_insert((entry.optional, entry.readonly));
    }
    let mut out: Vec<KeyInfo> = merged
      .into_iter()
      .map(|(key, (optional, readonly))| KeyInfo {
        key,
        optional,
        readonly,
      })
      .collect();
    out.sort_by(|a, b| a.key.cmp(&b.key, &self.store));
    out
  }

  fn evaluate_template_literal(
    &mut self,
    tpl: TemplateLiteralType,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    #[cfg(feature = "tracing")]
    let span = tracing::debug_span!(
      "types_ts_interned::TypeEvaluator::evaluate_template_literal",
      head_len = tpl.head.len() as u64,
      span_count = tpl.spans.len() as u64,
      computed = tracing::field::Empty,
      string_count = tracing::field::Empty,
      result = tracing::field::Empty,
    );
    #[cfg(feature = "tracing")]
    let _enter = span.enter();

    let strings = self.compute_template_strings(&tpl, subst, depth + 1);
    match strings {
      TemplateStringComputation::Finite(strings) => {
        #[cfg(feature = "tracing")]
        {
          span.record("computed", "finite");
          span.record("string_count", &(strings.len() as u64));
        }
        if strings.is_empty() {
          let result = self.store.primitive_ids().never;
          #[cfg(feature = "tracing")]
          {
            span.record("result", &tracing::field::debug(&result));
          }
          return result;
        }
        let mut types = Vec::new();
        for s in strings {
          let name = self.store.intern_name(s);
          types.push(self.store.intern_type(TypeKind::StringLiteral(name)));
        }
        let result = self.store.union(types);
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        result
      }
      TemplateStringComputation::TooLarge => {
        #[cfg(feature = "tracing")]
        {
          span.record("computed", "too_large");
        }
        let result = self.store.primitive_ids().string;
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        result
      }
      TemplateStringComputation::Infinite => {
        #[cfg(feature = "tracing")]
        {
          span.record("computed", "infinite");
        }
        let evaluated_spans = tpl
          .spans
          .into_iter()
          .map(|chunk| TemplateChunk {
            literal: chunk.literal,
            ty: self.evaluate_with_subst(chunk.ty, subst, depth + 1),
          })
          .collect();
        let result = self
          .store
          .intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
            head: tpl.head,
            spans: evaluated_spans,
          }));
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        result
      }
    }
  }

  fn evaluate_intrinsic(
    &mut self,
    kind: IntrinsicKind,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    let primitives = self.store.primitive_ids();
    let evaluated = self.evaluate_with_subst(ty, subst, depth + 1);

    match kind {
      IntrinsicKind::NoInfer => return evaluated,
      IntrinsicKind::BuiltinIteratorReturn => return primitives.any,
      _ => {}
    }

    match self.store.type_kind(evaluated) {
      TypeKind::Never => primitives.never,
      TypeKind::Any => primitives.any,
      // These intrinsics are defined with `extends string`, but we can still see
      // `unknown` during error recovery. Mirror TypeScript's behaviour by
      // widening to `string`.
      TypeKind::Unknown => primitives.string,
      TypeKind::Union(members) => {
        let mut out = Vec::with_capacity(members.len());
        for member in members {
          out.push(self.evaluate_intrinsic(kind, member, subst, depth + 1));
        }
        self.store.union(out)
      }
      TypeKind::StringLiteral(id) => {
        let mapped = apply_string_mapping(kind, &self.store.name(id));
        let name = self.store.intern_name(mapped);
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      TypeKind::TemplateLiteral(tpl) => {
        let TemplateLiteralType { head, spans } = tpl;

        match kind {
          IntrinsicKind::Uppercase => {
            let tpl = TemplateLiteralType {
              head: head.to_uppercase(),
              spans: spans
                .into_iter()
                .map(|span| TemplateChunk {
                  literal: span.literal.to_uppercase(),
                  ty: self.evaluate_intrinsic(kind, span.ty, subst, depth + 1),
                })
                .collect(),
            };
            self.store.intern_type(TypeKind::TemplateLiteral(tpl))
          }
          IntrinsicKind::Lowercase => {
            let tpl = TemplateLiteralType {
              head: head.to_lowercase(),
              spans: spans
                .into_iter()
                .map(|span| TemplateChunk {
                  literal: span.literal.to_lowercase(),
                  ty: self.evaluate_intrinsic(kind, span.ty, subst, depth + 1),
                })
                .collect(),
            };
            self.store.intern_type(TypeKind::TemplateLiteral(tpl))
          }
          IntrinsicKind::Capitalize => {
            let mut spans = spans;
            if head.is_empty() {
              if let Some(first) = spans.first_mut() {
                first.ty = self.evaluate_intrinsic(kind, first.ty, subst, depth + 1);
              }
            }
            let tpl = TemplateLiteralType {
              head: capitalize_string(&head),
              spans,
            };
            self.store.intern_type(TypeKind::TemplateLiteral(tpl))
          }
          IntrinsicKind::Uncapitalize => {
            let mut spans = spans;
            if head.is_empty() {
              if let Some(first) = spans.first_mut() {
                first.ty = self.evaluate_intrinsic(kind, first.ty, subst, depth + 1);
              }
            }
            let tpl = TemplateLiteralType {
              head: uncapitalize_string(&head),
              spans,
            };
            self.store.intern_type(TypeKind::TemplateLiteral(tpl))
          }
          IntrinsicKind::NoInfer => unreachable!("handled above"),
          IntrinsicKind::BuiltinIteratorReturn => unreachable!("handled above"),
        }
      }
      _ => self.store.intern_type(TypeKind::Intrinsic {
        kind,
        ty: evaluated,
      }),
    }
  }

  fn tuple_index_union(
    &mut self,
    elems: &[crate::kind::TupleElem],
    subst: &Substitution,
    depth: usize,
    options: crate::TypeOptions,
  ) -> TypeId {
    let mut members = Vec::new();
    for elem in elems.iter() {
      let mut ty = self.evaluate_with_subst(elem.ty, subst, depth + 1);
      if elem.optional && !options.exact_optional_property_types {
        ty = self
          .store
          .union(vec![ty, self.store.primitive_ids().undefined]);
      }
      members.push(ty);
    }
    self.store.union(members)
  }

  fn evaluate_indexed_access(
    &mut self,
    obj: TypeId,
    index: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    #[cfg(feature = "tracing")]
    let span = tracing::debug_span!(
      "types_ts_interned::TypeEvaluator::evaluate_indexed_access",
      obj = ?obj,
      index = ?index,
      result = tracing::field::Empty,
    );
    #[cfg(feature = "tracing")]
    let _enter = span.enter();

    let options = self.store.options();
    let obj_eval = self.evaluate_with_subst(obj, subst, depth + 1);
    let index_eval = self.evaluate_with_subst(index, subst, depth + 1);

    if let TypeKind::Union(keys) = self.store.type_kind(index_eval) {
      let mut results = Vec::new();
      for key in keys {
        results.push(self.evaluate_indexed_access(obj_eval, key, subst, depth + 1));
      }
      return self.store.union(results);
    }

    if let TypeKind::Union(objs) = self.store.type_kind(obj_eval) {
      let mut results = Vec::new();
      for member in objs {
        results.push(self.evaluate_indexed_access(member, index_eval, subst, depth + 1));
      }
      return self.store.union(results);
    }

    let mut result = match self.store.type_kind(obj_eval) {
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        match self.keys_from_index_type(index_eval) {
          KeySet::Known(keys) => {
            let mut hits = Vec::new();
            for key in keys {
              self.collect_property_type(&shape, &key, &mut hits, options);
            }
            if hits.is_empty() {
              self.store.primitive_ids().never
            } else {
              self.store.union(hits)
            }
          }
          KeySet::Unknown => self.store.primitive_ids().unknown,
        }
      }
      TypeKind::EmptyObject => match self.keys_from_index_type(index_eval) {
        // `{}` has no known keys, so any indexed access that successfully type
        // checks collapses to `never`.
        KeySet::Known(_) => self.store.primitive_ids().never,
        KeySet::Unknown => self.store.primitive_ids().unknown,
      },
      TypeKind::Array { ty, .. } => match self.store.type_kind(index_eval) {
        TypeKind::StringLiteral(id) if self.store.name(id) == "length" => {
          self.store.primitive_ids().number
        }
        TypeKind::NumberLiteral(_) | TypeKind::Number => {
          self.evaluate_with_subst(ty, subst, depth + 1)
        }
        TypeKind::StringLiteral(id) => {
          let key = PropKey::String(id);
          if parse_canonical_index_string(self.store.as_ref(), &key).is_some() {
            self.evaluate_with_subst(ty, subst, depth + 1)
          } else {
            self.store.primitive_ids().unknown
          }
        }
        _ => self.store.primitive_ids().unknown,
      },
      TypeKind::Tuple(elems) => match self.store.type_kind(index_eval) {
        TypeKind::StringLiteral(id) if self.store.name(id) == "length" => {
          if elems.iter().any(|elem| elem.rest) {
            self.store.primitive_ids().number
          } else {
            let len = elems.len();
            let mut required_len = len;
            while required_len > 0 && elems[required_len - 1].optional {
              required_len -= 1;
            }

            if required_len == len {
              self
                .store
                .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(len as f64)))
            } else {
              let mut members = Vec::new();
              for l in required_len..=len {
                members.push(
                  self
                    .store
                    .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(l as f64))),
                );
              }
              self.store.union(members)
            }
          }
        }
        TypeKind::NumberLiteral(num) => match number_literal_as_usize_index(num) {
          Some(idx) => {
            if let Some(elem) = elems.get(idx) {
              let mut ty = self.evaluate_with_subst(elem.ty, subst, depth + 1);
              if elem.optional && !options.exact_optional_property_types {
                ty = self
                  .store
                  .union(vec![ty, self.store.primitive_ids().undefined]);
              }
              ty
            } else {
              self.store.primitive_ids().undefined
            }
          }
          None => self.tuple_index_union(&elems, subst, depth, options),
        },
        TypeKind::StringLiteral(id) => {
          let key = PropKey::String(id);
          match parse_canonical_index_string(self.store.as_ref(), &key) {
            Some(idx) => match usize::try_from(idx) {
              Ok(idx) => {
                if let Some(elem) = elems.get(idx) {
                  let mut ty = self.evaluate_with_subst(elem.ty, subst, depth + 1);
                  if elem.optional && !options.exact_optional_property_types {
                    ty = self
                      .store
                      .union(vec![ty, self.store.primitive_ids().undefined]);
                  }
                  ty
                } else {
                  self.store.primitive_ids().undefined
                }
              }
              Err(_) => self.store.primitive_ids().undefined,
            },
            None => self.tuple_index_union(&elems, subst, depth, options),
          }
        }
        _ => self.tuple_index_union(&elems, subst, depth, options),
      },
      TypeKind::Intersection(members) => {
        // tsc: indexed access over an intersection gathers the property across
        // members (`(A & B)[K]` = `A[K] & B[K]` over the members that declare
        // K; members missing it contribute nothing) — `(Z & {})["a"]` is
        // `number`, needed for mapped types over `keyof (T & {})`.
        let mut hits = Vec::new();
        for member in members {
          let member_ty = self.evaluate_indexed_access(member, index_eval, subst, depth + 1);
          if !matches!(
            self.store.type_kind(self.store.canon(member_ty)),
            TypeKind::Never
          ) {
            hits.push(member_ty);
          }
        }
        if hits.is_empty() {
          self.store.primitive_ids().never
        } else {
          self.store.intersection(hits)
        }
      }
      _ => self.store.primitive_ids().unknown,
    };

    if options.no_unchecked_indexed_access {
      result = self
        .store
        .union(vec![result, self.store.primitive_ids().undefined]);
    }

    #[cfg(feature = "tracing")]
    {
      span.record("result", &tracing::field::debug(&result));
    }
    result
  }

  fn evaluate_keyof(&mut self, inner: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    #[cfg(feature = "tracing")]
    let span = tracing::debug_span!(
      "types_ts_interned::TypeEvaluator::evaluate_keyof",
      inner = ?inner,
      key_count = tracing::field::Empty,
      result = tracing::field::Empty,
    );
    #[cfg(feature = "tracing")]
    let _enter = span.enter();

    let keyset = self.keys_from_type(inner, subst, depth + 1);
    match keyset {
      KeySet::Known(keys) => {
        #[cfg(feature = "tracing")]
        {
          span.record("key_count", &(keys.len() as u64));
        }
        let mut members = Vec::new();
        for key in keys {
          match key {
            Key::Literal(PropKey::String(id)) => {
              members.push(self.store.intern_type(TypeKind::StringLiteral(id)));
            }
            Key::Literal(PropKey::Number(num)) => {
              members.push(
                self
                  .store
                  .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(num as f64))),
              );
            }
            Key::Literal(PropKey::Symbol(_)) => members.push(self.store.primitive_ids().symbol),
            Key::String => members.push(self.store.primitive_ids().string),
            Key::Number => members.push(self.store.primitive_ids().number),
            Key::Symbol => members.push(self.store.primitive_ids().symbol),
          }
        }
        let result = self.store.union(members);
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        result
      }
      KeySet::Unknown => {
        #[cfg(feature = "tracing")]
        {
          span.record("key_count", &0u64);
        }
        let result = self.store.union(vec![
          self.store.primitive_ids().string,
          self.store.primitive_ids().number,
          self.store.primitive_ids().symbol,
        ]);
        #[cfg(feature = "tracing")]
        {
          span.record("result", &tracing::field::debug(&result));
        }
        result
      }
    }
  }

  fn keys_from_index_type(&mut self, ty: TypeId) -> KeySet {
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut keys = Vec::new();
        for member in members {
          match self.keys_from_index_type(member) {
            KeySet::Known(mut inner) => keys.append(&mut inner),
            KeySet::Unknown => return KeySet::Unknown,
          }
        }
        KeySet::known(keys, &self.store)
      }
      TypeKind::Never => KeySet::known(Vec::new(), &self.store),
      TypeKind::StringLiteral(id) => {
        KeySet::known(vec![Key::Literal(PropKey::String(id))], &self.store)
      }
      TypeKind::NumberLiteral(num) => match number_literal_as_i64(num) {
        Some(num) => KeySet::known(vec![Key::Literal(PropKey::Number(num))], &self.store),
        None => KeySet::known(vec![Key::Number], &self.store),
      },
      TypeKind::Symbol | TypeKind::UniqueSymbol => KeySet::known(vec![Key::Symbol], &self.store),
      TypeKind::TemplateLiteral(tpl) => {
        match self.compute_template_strings(&tpl, &Substitution::empty(), 0) {
          TemplateStringComputation::Finite(strings) => KeySet::known(
            strings
              .into_iter()
              .map(|s| Key::Literal(PropKey::String(self.store.intern_name(s))))
              .collect(),
            &self.store,
          ),
          TemplateStringComputation::Infinite | TemplateStringComputation::TooLarge => {
            KeySet::known(vec![Key::String], &self.store)
          }
        }
      }
      TypeKind::String => KeySet::known(vec![Key::String], &self.store),
      TypeKind::Number => KeySet::known(vec![Key::Number], &self.store),
      _ => KeySet::Unknown,
    }
  }

  fn keys_from_type(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> KeySet {
    let evaluated = self.evaluate_with_subst(ty, subst, depth + 1);
    self.keys_from_type_id(evaluated, subst, depth + 1)
  }

  fn keys_from_type_as_entries(
    &mut self,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> Vec<KeyInfo> {
    match self.store.type_kind(ty) {
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        let mut merged: AHashMap<Key, (bool, bool)> = AHashMap::new();
        for prop in shape.properties.iter() {
          merged
            .entry(Key::Literal(prop.key.clone()))
            .and_modify(|entry| {
              entry.0 |= prop.data.optional;
              entry.1 |= prop.data.readonly;
            })
            .or_insert((prop.data.optional, prop.data.readonly));
        }
        let dummy_name = self.store.intern_name("");
        for idxer in shape.indexers.iter() {
          // Index signatures can use non-primitive key types (e.g. `(string | number) & string`),
          // so derive the broad keys they accept by probing with representative property keys.
          let mut keys = Vec::new();
          if self.indexer_accepts_key(&PropKey::String(dummy_name), idxer.key_type) {
            keys.push(Key::String);
          }
          if self.indexer_accepts_key(&PropKey::Number(0), idxer.key_type) {
            keys.push(Key::Number);
          }
          if self.indexer_accepts_key(&PropKey::Symbol(dummy_name), idxer.key_type) {
            keys.push(Key::Symbol);
          }
          for key in keys {
            merged
              .entry(key.clone())
              .and_modify(|entry| entry.1 |= idxer.readonly)
              .or_insert((false, idxer.readonly));
          }
        }
        let mut entries: Vec<KeyInfo> = merged
          .into_iter()
          .map(|(key, (optional, readonly))| KeyInfo {
            key,
            optional,
            readonly,
          })
          .collect();
        entries.sort_by(|a, b| a.key.cmp(&b.key, &self.store));
        entries
      }
      _ => match self.keys_from_type_id(ty, subst, depth) {
        KeySet::Known(keys) => keys
          .into_iter()
          .map(|key| KeyInfo {
            key,
            optional: false,
            readonly: false,
          })
          .collect(),
        KeySet::Unknown => {
          let mut entries = vec![
            KeyInfo {
              key: Key::String,
              optional: false,
              readonly: false,
            },
            KeyInfo {
              key: Key::Number,
              optional: false,
              readonly: false,
            },
            KeyInfo {
              key: Key::Symbol,
              optional: false,
              readonly: false,
            },
          ];
          entries.sort_by(|a, b| a.key.cmp(&b.key, &self.store));
          entries
        }
      },
    }
  }

  fn keys_from_type_id(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> KeySet {
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut iter = members.into_iter();
        let Some(first) = iter.next() else {
          return KeySet::known(Vec::new(), &self.store);
        };
        let mut acc = self.keys_from_type(first, subst, depth + 1);
        for member in iter {
          acc = acc.intersect(self.keys_from_type(member, subst, depth + 1), &self.store);
        }
        acc
      }
      TypeKind::Intersection(members) => {
        let mut acc = KeySet::known(Vec::new(), &self.store);
        for member in members {
          let keys = self.keys_from_type(member, subst, depth + 1);
          acc = acc.union(keys, &self.store);
        }
        acc
      }
      // tsc `getIndexType`: `keyof never` is the keyof constraint type
      // `string | number | symbol`, not `never` (verified against tsc 5.9.3).
      // `KeySet::Unknown` produces exactly that union in `evaluate_keyof`, and
      // acts as the universal set in key-set intersection, so
      // `keyof (A | never)` still reduces to `keyof A`.
      TypeKind::Never => KeySet::Unknown,
      TypeKind::Unknown | TypeKind::EmptyObject => KeySet::Known(Vec::new()),
      TypeKind::Object(obj) => {
        let mut keys = Vec::new();
        let shape = self.store.shape(self.store.object(obj).shape);
        for prop in shape.properties.iter() {
          // ES private identifiers (`#foo`) are never keys (tsc:
          // `privateNamesAndkeyof.ts` — `keyof A` excludes private members).
          if let PropKey::String(name) = &prop.key {
            if self.store.name(*name).starts_with('#') {
              continue;
            }
          }
          keys.push(Key::Literal(prop.key.clone()));
        }
        let dummy_name = self.store.intern_name("");
        for idx in shape.indexers.iter() {
          if self.indexer_accepts_key(&PropKey::String(dummy_name), idx.key_type) {
            keys.push(Key::String);
          }
          if self.indexer_accepts_key(&PropKey::Number(0), idx.key_type) {
            keys.push(Key::Number);
          }
          if self.indexer_accepts_key(&PropKey::Symbol(dummy_name), idx.key_type) {
            keys.push(Key::Symbol);
          }
        }
        KeySet::known(keys, &self.store)
      }
      TypeKind::Tuple(elems) => {
        let mut keys = Vec::new();
        for (idx, elem) in elems.iter().enumerate() {
          keys.push(Key::Literal(PropKey::Number(idx as i64)));
          if elem.rest {
            keys.push(Key::Number);
            break;
          }
        }
        KeySet::known(keys, &self.store)
      }
      TypeKind::Array { .. } => KeySet::known(vec![Key::Number], &self.store),
      TypeKind::TemplateLiteral(tpl) => {
        match self.compute_template_strings(&tpl, subst, depth + 1) {
          TemplateStringComputation::Finite(strings) => KeySet::known(
            strings
              .into_iter()
              .map(|s| Key::Literal(PropKey::String(self.store.intern_name(s))))
              .collect(),
            &self.store,
          ),
          TemplateStringComputation::Infinite | TemplateStringComputation::TooLarge => {
            KeySet::known(vec![Key::String], &self.store)
          }
        }
      }
      TypeKind::StringLiteral(id) => {
        KeySet::known(vec![Key::Literal(PropKey::String(id))], &self.store)
      }
      TypeKind::NumberLiteral(num) => match number_literal_as_i64(num) {
        Some(num) => KeySet::known(vec![Key::Literal(PropKey::Number(num))], &self.store),
        None => KeySet::known(vec![Key::Number], &self.store),
      },
      TypeKind::UniqueSymbol => KeySet::known(vec![Key::Symbol], &self.store),
      TypeKind::Symbol => KeySet::known(vec![Key::Symbol], &self.store),
      TypeKind::String => KeySet::known(vec![Key::String], &self.store),
      TypeKind::Number => KeySet::known(vec![Key::Number], &self.store),
      _ => KeySet::Unknown,
    }
  }

  fn collect_property_type(
    &self,
    shape: &Shape,
    key: &Key,
    hits: &mut Vec<TypeId>,
    options: crate::TypeOptions,
  ) {
    for prop in shape.properties.iter() {
      // ES private identifier keys (`#foo`) are not visible to indexed access /
      // `keyof` string lookup (tsc: `C["#foo"]` → nonexistent property).
      if let PropKey::String(name) = &prop.key {
        if self.store.name(*name).starts_with('#') {
          continue;
        }
      }
      if match (key, &prop.key) {
        (Key::Literal(a), b) => prop_keys_equal_for_lookup(self.store.as_ref(), a, b),
        (Key::String, PropKey::String(_)) => true,
        (Key::Number, PropKey::Number(_)) => true,
        (Key::Symbol, PropKey::Symbol(_)) => true,
        _ => false,
      } {
        let mut ty = prop.data.ty;
        if prop.data.optional && !options.exact_optional_property_types {
          ty = self
            .store
            .union(vec![ty, self.store.primitive_ids().undefined]);
        }
        hits.push(ty);
      }
    }
    for idxer in shape.indexers.iter() {
      let matches = match key {
        Key::Literal(prop_key) => self.indexer_accepts_key(prop_key, idxer.key_type),
        Key::String => {
          self.indexer_accepts_key(
            &PropKey::String(self.store.intern_name(String::new())),
            idxer.key_type,
          ) || self.indexer_accepts_key(&PropKey::Number(0), idxer.key_type)
        }
        Key::Number => self.indexer_accepts_key(&PropKey::Number(0), idxer.key_type),
        Key::Symbol => self.indexer_accepts_key(
          &PropKey::Symbol(self.store.intern_name(String::new())),
          idxer.key_type,
        ),
      };
      if matches {
        hits.push(idxer.value_type);
      }
    }
  }

  fn indexer_accepts_key(&self, key: &PropKey, idx_key: TypeId) -> bool {
    self.indexer_accepts_key_inner(key, idx_key, 0)
  }

  fn indexer_accepts_key_inner(&self, key: &PropKey, idx_key: TypeId, depth: usize) -> bool {
    if depth >= self.limits.depth_limit {
      return false;
    }

    match self.store.type_kind(idx_key) {
      TypeKind::String | TypeKind::StringLiteral(_) => {
        matches!(key, PropKey::String(_) | PropKey::Number(_))
      }
      TypeKind::Number | TypeKind::NumberLiteral(_) => match key {
        PropKey::Number(_) => true,
        PropKey::String(_) => parse_canonical_index_string(self.store.as_ref(), key).is_some(),
        _ => false,
      },
      TypeKind::Symbol | TypeKind::UniqueSymbol => matches!(key, PropKey::Symbol(_)),
      TypeKind::Union(members) => members
        .iter()
        .any(|member| self.indexer_accepts_key_inner(key, *member, depth + 1)),
      TypeKind::Intersection(members) => members
        .iter()
        .all(|member| self.indexer_accepts_key_inner(key, *member, depth + 1)),
      _ => false,
    }
  }

  fn compute_template_strings(
    &mut self,
    tpl: &TemplateLiteralType,
    subst: &Substitution,
    depth: usize,
  ) -> TemplateStringComputation {
    // First determine whether all template atoms are finite. Any non-finite atom
    // makes the whole template non-enumerable (`Infinite`), while atoms that are
    // finite-but-too-large should still bail out to `string` (`TooLarge`).
    let mut saw_too_large_atom = false;
    let mut atom_strings: Vec<Vec<String>> = Vec::with_capacity(tpl.spans.len());
    for span in tpl.spans.iter() {
      match self.template_atom_strings(span.ty, subst, depth + 1) {
        TemplateStringComputation::Finite(strings) => atom_strings.push(strings),
        TemplateStringComputation::Infinite => return TemplateStringComputation::Infinite,
        TemplateStringComputation::TooLarge => {
          saw_too_large_atom = true;
          atom_strings.push(Vec::new());
        }
      }
    }
    if saw_too_large_atom {
      return TemplateStringComputation::TooLarge;
    }

    let mut acc = vec![tpl.head.clone()];
    for (span, atom_strings) in tpl.spans.iter().zip(atom_strings.into_iter()) {
      if acc.is_empty() {
        break;
      }
      if atom_strings.is_empty() {
        acc.clear();
        break;
      }
      match acc.len().checked_mul(atom_strings.len()) {
        Some(product) if product <= self.limits.max_template_strings => {}
        _ => return TemplateStringComputation::TooLarge,
      }
      let mut next = Vec::new();
      for base in &acc {
        for atom in &atom_strings {
          if next.len() >= self.limits.max_template_strings {
            return TemplateStringComputation::TooLarge;
          }
          let mut new = base.clone();
          new.push_str(atom);
          new.push_str(&span.literal);
          next.push(new);
        }
      }
      acc = next;
    }
    if acc.len() > self.limits.max_template_strings {
      return TemplateStringComputation::TooLarge;
    }
    acc.sort();
    acc.dedup();
    TemplateStringComputation::Finite(acc)
  }

  fn template_atom_strings(
    &mut self,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> TemplateStringComputation {
    let evaluated = self.evaluate_with_subst(ty, subst, depth + 1);
    match self.store.type_kind(evaluated) {
      TypeKind::StringLiteral(id) => TemplateStringComputation::Finite(vec![self.store.name(id)]),
      TypeKind::NumberLiteral(num) => TemplateStringComputation::Finite(vec![num.0.to_string()]),
      TypeKind::BooleanLiteral(val) => TemplateStringComputation::Finite(vec![val.to_string()]),
      TypeKind::TemplateLiteral(tpl) => self.compute_template_strings(&tpl, subst, depth + 1),
      TypeKind::Union(members) => {
        let mut out = Vec::new();
        let mut saw_too_large = false;
        for member in members {
          match self.template_atom_strings(member, subst, depth + 1) {
            TemplateStringComputation::Finite(mut vals) => {
              if !saw_too_large {
                out.append(&mut vals);
                if out.len() > self.limits.max_template_strings {
                  saw_too_large = true;
                  out.clear();
                }
              }
            }
            TemplateStringComputation::Infinite => return TemplateStringComputation::Infinite,
            TemplateStringComputation::TooLarge => saw_too_large = true,
          }
        }
        if saw_too_large {
          TemplateStringComputation::TooLarge
        } else {
          TemplateStringComputation::Finite(out)
        }
      }
      TypeKind::Never => TemplateStringComputation::Finite(Vec::new()),
      _ => TemplateStringComputation::Infinite,
    }
  }
}

fn apply_string_mapping(kind: IntrinsicKind, value: &str) -> String {
  match kind {
    IntrinsicKind::Uppercase => value.to_uppercase(),
    IntrinsicKind::Lowercase => value.to_lowercase(),
    IntrinsicKind::Capitalize => capitalize_string(value),
    IntrinsicKind::Uncapitalize => uncapitalize_string(value),
    IntrinsicKind::NoInfer => value.to_string(),
    IntrinsicKind::BuiltinIteratorReturn => value.to_string(),
  }
}

fn capitalize_string(value: &str) -> String {
  let mut chars = value.chars();
  match chars.next() {
    None => String::new(),
    Some(first) => {
      let mut out: String = first.to_uppercase().collect();
      out.push_str(chars.as_str());
      out
    }
  }
}

fn uncapitalize_string(value: &str) -> String {
  let mut chars = value.chars();
  match chars.next() {
    None => String::new(),
    Some(first) => {
      let mut out: String = first.to_lowercase().collect();
      out.push_str(chars.as_str());
      out
    }
  }
}

#[derive(Clone, Debug)]
enum TemplateStringComputation {
  Finite(Vec<String>),
  Infinite,
  TooLarge,
}

struct MappedKeyTypes {
  original: TypeId,
}

fn prop_keys_equal_for_lookup(store: &TypeStore, a: &PropKey, b: &PropKey) -> bool {
  if a == b {
    return true;
  }
  match (a, b) {
    (PropKey::String(_), PropKey::Number(num)) => {
      parse_canonical_index_string(store, a) == Some(*num)
    }
    (PropKey::Number(num), PropKey::String(_)) => {
      parse_canonical_index_string(store, b) == Some(*num)
    }
    _ => false,
  }
}

fn parse_canonical_index_string(store: &TypeStore, key: &PropKey) -> Option<i64> {
  let PropKey::String(id) = key else {
    return None;
  };
  parse_canonical_index_str(&store.name(*id))
}

fn number_literal_as_i64(num: OrderedFloat<f64>) -> Option<i64> {
  let value = num.0;
  if !value.is_finite() {
    return None;
  }
  if value.fract() != 0.0 {
    return None;
  }
  if value < i64::MIN as f64 || value >= i64::MAX as f64 {
    return None;
  }
  Some(value as i64)
}

fn number_literal_as_usize_index(num: OrderedFloat<f64>) -> Option<usize> {
  usize::try_from(number_literal_as_i64(num)?).ok()
}

fn parse_canonical_index_str(s: &str) -> Option<i64> {
  if s == "0" {
    return Some(0);
  }
  let bytes = s.as_bytes();
  let first = *bytes.first()?;
  if first == b'0' {
    return None;
  }
  if bytes.iter().all(|c| c.is_ascii_digit()) {
    s.parse().ok()
  } else {
    None
  }
}
