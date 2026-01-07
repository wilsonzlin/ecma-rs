use crate::cache::{CacheConfig, CacheStats, ShardedCache};
use crate::eval::ConditionalAssignability;
use crate::eval::EvaluatorCacheStats;
use crate::eval::EvaluatorCaches;
use crate::eval::ExpandedType;
use crate::eval::TypeEvaluator;
use crate::eval::TypeExpander as EvalTypeExpander;
use crate::shape::Indexer;
use crate::shape::Property;
use crate::shape::Shape;
use crate::signature::{Signature, TypeParamDecl, TypeParamVariance};
use crate::Accessibility;
use crate::DefId;
use crate::IntrinsicKind;
use crate::ObjectId;
use crate::PropData;
use crate::PropKey;
use crate::SignatureId;
use crate::TypeId;
use crate::TypeKind;
use crate::TypeOptions;
use crate::TypeStore;
use bitflags::bitflags;
use std::cell::{Cell, RefCell};
use std::collections::{HashSet, VecDeque};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
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

#[cfg(test)]
thread_local! {
  static NORMALIZE_CALLS: Cell<usize> = const { Cell::new(0) };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RelationKind {
  Assignable,
  Comparable,
  StrictSubtype,
}

bitflags! {
  #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
  pub struct RelationMode: u8 {
    const NONE = 0;
    const BIVARIANT_PARAMS = 1 << 0;
    /// Skip normalization (`RelateCtx::normalize_type`) in [`RelateCtx::assignable`].
    ///
    /// This exists to break potential relate <-> evaluate cycles when
    /// conditional type evaluation needs to ask the relation engine whether the
    /// evaluated `check` type is assignable to the evaluated `extends` type.
    const SKIP_NORMALIZE = 1 << 1;
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationResult {
  pub result: bool,
  pub reason: Option<ReasonNode>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ReasonNode {
  pub src: TypeId,
  pub dst: TypeId,
  pub relation: RelationKind,
  pub outcome: bool,
  pub note: Option<String>,
  pub children: Vec<ReasonNode>,
}

const MAX_REASON_DEPTH: usize = 12;
const MAX_REASON_NODES: usize = 256;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RelationLimits {
  /// Maximum number of relation steps before conservatively assuming success.
  ///
  /// Use `usize::MAX` to disable step tracking entirely (the default).
  pub step_limit: usize,
  /// Maximum recursion depth for `RelateCtx::relate_internal`.
  pub max_relation_depth: usize,
  /// Maximum number of entries in the `in_progress` relation set.
  pub max_in_progress: usize,
  /// Maximum recursion depth when matching indexer keys.
  pub max_indexer_key_match_depth: usize,
  /// Maximum recursion depth when enumerating or matching template literal atoms.
  pub max_template_match_depth: usize,
  /// Maximum number of explored states when matching a string against a template literal.
  pub max_template_match_states: usize,
  /// Maximum number of concrete strings produced when enumerating template literal atoms.
  pub max_template_atom_strings: usize,
}

impl RelationLimits {
  pub const DEFAULT_STEP_LIMIT: usize = usize::MAX;
  pub const DEFAULT_MAX_RELATION_DEPTH: usize = 64;
  pub const DEFAULT_MAX_IN_PROGRESS: usize = 128;
  pub const DEFAULT_MAX_INDEXER_KEY_MATCH_DEPTH: usize = 64;
  pub const DEFAULT_MAX_TEMPLATE_MATCH_DEPTH: usize = 32;
  pub const DEFAULT_MAX_TEMPLATE_MATCH_STATES: usize = 1024;
  pub const DEFAULT_MAX_TEMPLATE_ATOM_STRINGS: usize = 1024;
}

impl Default for RelationLimits {
  fn default() -> Self {
    Self {
      step_limit: Self::DEFAULT_STEP_LIMIT,
      max_relation_depth: Self::DEFAULT_MAX_RELATION_DEPTH,
      max_in_progress: Self::DEFAULT_MAX_IN_PROGRESS,
      max_indexer_key_match_depth: Self::DEFAULT_MAX_INDEXER_KEY_MATCH_DEPTH,
      max_template_match_depth: Self::DEFAULT_MAX_TEMPLATE_MATCH_DEPTH,
      max_template_match_states: Self::DEFAULT_MAX_TEMPLATE_MATCH_STATES,
      max_template_atom_strings: Self::DEFAULT_MAX_TEMPLATE_ATOM_STRINGS,
    }
  }
}

#[derive(Default, Debug)]
struct ReasonBudget {
  nodes: usize,
}

#[derive(Clone, Copy, Debug)]
enum OptionalFlavor {
  Property,
  Parameter,
  TupleElement,
  IndexerValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PropKeyKind {
  String,
  Number,
  Symbol,
}

pub struct RelateHooks<'a> {
  pub expander: Option<&'a dyn RelateTypeExpander>,
  pub is_same_origin_private_member: Option<&'a dyn Fn(&Property, &Property) -> bool>,
}

impl<'a> fmt::Debug for RelateHooks<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RelateHooks")
      .field(
        "expander",
        &self.expander.as_ref().map(|_| "RelateTypeExpander"),
      )
      .field(
        "is_same_origin_private_member",
        &self.is_same_origin_private_member.as_ref().map(|_| "Fn"),
      )
      .finish()
  }
}

impl<'a> Default for RelateHooks<'a> {
  fn default() -> Self {
    Self {
      expander: None,
      is_same_origin_private_member: None,
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RelationKey {
  src: TypeId,
  dst: TypeId,
  kind: RelationKind,
  mode: RelationMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GenRelationKey {
  gen: u64,
  key: RelationKey,
}

#[derive(Clone, Debug)]
pub struct RelationCache {
  generation: Arc<AtomicU64>,
  inner: Arc<ShardedCache<GenRelationKey, bool>>,
}

impl Default for RelationCache {
  fn default() -> Self {
    Self::new(CacheConfig::default())
  }
}

impl RelationCache {
  pub fn new(config: CacheConfig) -> Self {
    Self {
      generation: Arc::new(AtomicU64::new(0)),
      inner: Arc::new(ShardedCache::new(config)),
    }
  }

  pub fn invalidate(&self) {
    self.generation.fetch_add(1, Ordering::Relaxed);
  }

  pub fn stats(&self) -> CacheStats {
    self.inner.stats()
  }

  pub fn len(&self) -> usize {
    self.inner.len()
  }

  fn get(&self, key: &RelationKey) -> Option<bool> {
    let gen = self.generation.load(Ordering::Relaxed);
    let key = GenRelationKey { gen, key: *key };
    self.inner.get(&key)
  }

  fn insert(&self, key: RelationKey, value: bool) {
    let gen = self.generation.load(Ordering::Relaxed);
    self.inner.insert(GenRelationKey { gen, key }, value);
  }

  pub fn clear(&self) {
    self.inner.clear();
  }
}

pub trait RelateTypeExpander {
  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId>;

  fn type_param_decls(&self, _def: DefId) -> Option<Arc<[TypeParamDecl]>> {
    None
  }
}

struct RelateExpanderAdapter<'a> {
  hook: Option<&'a dyn RelateTypeExpander>,
}

impl<'a> EvalTypeExpander for RelateExpanderAdapter<'a> {
  fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType> {
    self
      .hook
      .and_then(|expander| expander.expand_ref(store, def, args))
      .map(|ty| ExpandedType {
        params: Vec::new(),
        ty,
      })
  }
}

pub struct RelateCtx<'a> {
  store: Arc<TypeStore>,
  pub options: TypeOptions,
  hooks: RelateHooks<'a>,
  cache: RelationCache,
  normalizer_caches: EvaluatorCaches,
  in_progress: RefCell<HashSet<RelationKey>>,
  reason_budget: RefCell<ReasonBudget>,
  limits: RelationLimits,
  steps: Cell<usize>,
}

impl<'a> fmt::Debug for RelateCtx<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RelateCtx")
      .field("options", &self.options)
      .field("limits", &self.limits)
      .finish()
  }
}

impl<'a> RelateCtx<'a> {
  /// Create a new [`RelateCtx`].
  ///
  /// `options.exact_optional_property_types` and `options.no_unchecked_indexed_access`
  /// must match [`TypeStore::options`] because type normalization uses
  /// [`TypeEvaluator`], which reads these evaluation-affecting flags from the
  /// store. Other options (e.g. `strict_null_checks` and `strict_function_types`)
  /// only affect relation and may differ from the store.
  pub fn new(store: Arc<TypeStore>, options: TypeOptions) -> Self {
    Self::with_options(store, options)
  }

  /// Create a new [`RelateCtx`] with the given [`TypeOptions`].
  ///
  /// See [`RelateCtx::new`] for invariants around evaluation-affecting options.
  pub fn with_options(store: Arc<TypeStore>, options: TypeOptions) -> Self {
    Self::with_hooks(store, options, RelateHooks::default())
  }

  pub fn with_hooks(store: Arc<TypeStore>, options: TypeOptions, hooks: RelateHooks<'a>) -> Self {
    Self::with_hooks_and_cache(store, options, hooks, RelationCache::default())
  }

  pub fn with_cache(store: Arc<TypeStore>, options: TypeOptions, cache: RelationCache) -> Self {
    Self::with_hooks_and_cache(store, options, RelateHooks::default(), cache)
  }

  pub fn with_cache_config(
    store: Arc<TypeStore>,
    options: TypeOptions,
    cache: CacheConfig,
  ) -> Self {
    Self::with_hooks_and_cache(
      store,
      options,
      RelateHooks::default(),
      RelationCache::new(cache),
    )
  }

  pub fn with_hooks_and_cache(
    store: Arc<TypeStore>,
    options: TypeOptions,
    hooks: RelateHooks<'a>,
    cache: RelationCache,
  ) -> Self {
    Self::with_hooks_cache_and_normalizer_caches(
      store,
      options,
      hooks,
      cache,
      EvaluatorCaches::new(CacheConfig::default()),
    )
  }

  /// Create a new [`RelateCtx`] with explicit relation and normalization caches.
  ///
  /// This is primarily useful for parallel type checking. A checker can create
  /// an [`EvaluatorCaches`] instance once and clone it into multiple
  /// per-thread [`RelateCtx`] instances, allowing `TypeEvaluator` normalization
  /// work to be reused across contexts.
  ///
  /// ## Correctness requirements
  ///
  /// `normalizer_caches` memoizes results of [`RelateCtx::normalize_type`] (via
  /// [`TypeEvaluator`]) and is keyed only by [`TypeId`]. It must therefore only
  /// be shared between `RelateCtx` instances that:
  /// - use the same [`TypeStore`] (or an equivalent store containing all
  ///   referenced types), and
  /// - use semantically equivalent `options` and `hooks` (notably the reference
  ///   expander and conditional-type assignability rules).
  pub fn with_hooks_cache_and_normalizer_caches(
    store: Arc<TypeStore>,
    options: TypeOptions,
    hooks: RelateHooks<'a>,
    cache: RelationCache,
    normalizer_caches: EvaluatorCaches,
  ) -> Self {
    let store_options = store.options();
    debug_assert_eq!(
      options.exact_optional_property_types, store_options.exact_optional_property_types,
      concat!(
        "RelateCtx.options.exact_optional_property_types must match ",
        "TypeStore.options().exact_optional_property_types because type normalization uses ",
        "TypeEvaluator, which reads evaluation-affecting options from the TypeStore."
      )
    );
    debug_assert_eq!(
      options.no_unchecked_indexed_access, store_options.no_unchecked_indexed_access,
      concat!(
        "RelateCtx.options.no_unchecked_indexed_access must match ",
        "TypeStore.options().no_unchecked_indexed_access because type normalization uses ",
        "TypeEvaluator, which reads evaluation-affecting options from the TypeStore."
      )
    );

    Self {
      store,
      options,
      hooks,
      cache,
      normalizer_caches,
      in_progress: RefCell::new(HashSet::new()),
      reason_budget: RefCell::new(ReasonBudget::default()),
      limits: RelationLimits::default(),
      steps: Cell::new(0),
    }
  }

  pub fn with_limits(mut self, limits: RelationLimits) -> Self {
    self.limits = limits;
    self
  }

  pub fn limits(&self) -> RelationLimits {
    self.limits
  }

  pub fn with_step_limit(mut self, limit: usize) -> Self {
    self.limits.step_limit = limit;
    self
  }

  pub fn step_count(&self) -> usize {
    self.steps.get()
  }

  pub fn cache_stats(&self) -> CacheStats {
    self.cache.stats()
  }

  pub fn normalizer_cache_stats(&self) -> EvaluatorCacheStats {
    self.normalizer_caches.stats()
  }

  pub fn clear_cache(&self) {
    self.cache.clear();
  }

  pub fn cache_len(&self) -> usize {
    self.cache.len()
  }

  pub fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    #[cfg(feature = "tracing")]
    {
      let span = tracing::info_span!(
        "types_ts_interned::RelateCtx::is_assignable",
        src = ?src,
        dst = ?dst,
        kind = ?RelationKind::Assignable,
        mode = ?RelationMode::NONE,
        step_limit = self.limits.step_limit as u64,
        result = tracing::field::Empty,
        cache_hit = false,
        depth_limit_hit = false,
        step_limit_hit = false,
      );
      let _enter = span.enter();
      let result = self
        .relate_internal(
          src,
          dst,
          RelationKind::Assignable,
          RelationMode::NONE,
          false,
          0,
        )
        .result;
      span.record("result", &result);
      result
    }

    #[cfg(not(feature = "tracing"))]
    self
      .relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::NONE,
        false,
        0,
      )
      .result
  }

  pub(crate) fn is_assignable_no_normalize(&self, src: TypeId, dst: TypeId) -> bool {
    self
      .relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::SKIP_NORMALIZE,
        false,
        0,
      )
      .result
  }

  pub fn explain_assignable(&self, src: TypeId, dst: TypeId) -> RelationResult {
    #[cfg(feature = "tracing")]
    {
      let span = tracing::info_span!(
        "types_ts_interned::RelateCtx::explain_assignable",
        src = ?src,
        dst = ?dst,
        kind = ?RelationKind::Assignable,
        mode = ?RelationMode::NONE,
        step_limit = self.limits.step_limit as u64,
        result = tracing::field::Empty,
        cache_hit = false,
        depth_limit_hit = false,
        step_limit_hit = false,
      );
      let _enter = span.enter();
      self.reset_reason_budget();
      let result = self.relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::NONE,
        true,
        0,
      );
      span.record("result", &result.result);
      result
    }

    #[cfg(not(feature = "tracing"))]
    {
      self.reset_reason_budget();
      self.relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::NONE,
        true,
        0,
      )
    }
  }

  pub fn is_comparable(&self, a: TypeId, b: TypeId) -> bool {
    #[cfg(feature = "tracing")]
    {
      let span = tracing::info_span!(
        "types_ts_interned::RelateCtx::is_comparable",
        src = ?a,
        dst = ?b,
        kind = ?RelationKind::Comparable,
        mode = ?RelationMode::NONE,
        step_limit = self.limits.step_limit as u64,
        result = tracing::field::Empty,
        cache_hit = false,
        depth_limit_hit = false,
        step_limit_hit = false,
      );
      let _enter = span.enter();
      let result = self
        .relate_internal(a, b, RelationKind::Comparable, RelationMode::NONE, false, 0)
        .result;
      span.record("result", &result);
      result
    }

    #[cfg(not(feature = "tracing"))]
    self
      .relate_internal(a, b, RelationKind::Comparable, RelationMode::NONE, false, 0)
      .result
  }

  pub fn is_strict_subtype(&self, src: TypeId, dst: TypeId) -> bool {
    #[cfg(feature = "tracing")]
    {
      let span = tracing::info_span!(
        "types_ts_interned::RelateCtx::is_strict_subtype",
        src = ?src,
        dst = ?dst,
        kind = ?RelationKind::StrictSubtype,
        mode = ?RelationMode::NONE,
        step_limit = self.limits.step_limit as u64,
        result = tracing::field::Empty,
        cache_hit = false,
        depth_limit_hit = false,
        step_limit_hit = false,
      );
      let _enter = span.enter();
      let result = self
        .relate_internal(
          src,
          dst,
          RelationKind::StrictSubtype,
          RelationMode::NONE,
          false,
          0,
        )
        .result;
      span.record("result", &result);
      result
    }

    #[cfg(not(feature = "tracing"))]
    self
      .relate_internal(
        src,
        dst,
        RelationKind::StrictSubtype,
        RelationMode::NONE,
        false,
        0,
      )
      .result
  }

  fn relate_internal(
    &self,
    src: TypeId,
    dst: TypeId,
    kind: RelationKind,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    if depth == 0 && self.limits.step_limit != RelationLimits::DEFAULT_STEP_LIMIT {
      self.steps.set(0);
    }

    let key = RelationKey {
      src,
      dst,
      kind,
      mode,
    };
    if depth >= self.limits.max_relation_depth {
      #[cfg(feature = "tracing")]
      {
        let span = tracing::Span::current();
        span.record("depth_limit_hit", &true);
      }
      let record = record && self.take_reason_slot();
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          true,
          Some("depth limit".into()),
          depth,
        ),
      };
    }
    if let Some(hit) = self.cache.get(&key) {
      #[cfg(feature = "tracing")]
      {
        if depth == 0 {
          let span = tracing::Span::current();
          span.record("cache_hit", &true);
          span.record("result", &hit);
        }
      }
      let record = record && self.take_reason_slot();
      return RelationResult {
        result: hit,
        reason: self.cached_reason(record, key, hit, depth),
      };
    }
    if self.in_progress.borrow().contains(&key) {
      // Structural relations in TypeScript assume success on cycles to break
      // infinite recursion. We mirror that here.
      let record = record && self.take_reason_slot();
      return RelationResult {
        result: true,
        reason: self.cycle_reason(record, key, depth),
      };
    }

    if self.limits.step_limit != RelationLimits::DEFAULT_STEP_LIMIT {
      let current_steps = self.steps.get();
      if current_steps >= self.limits.step_limit {
        #[cfg(feature = "tracing")]
        {
          let span = tracing::Span::current();
          span.record("step_limit_hit", &true);
        }
        let record = record && self.take_reason_slot();
        return RelationResult {
          result: true,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            true,
            Some("step limit".into()),
            depth,
          ),
        };
      }
      self.steps.set(current_steps + 1);
    }

    if self.in_progress.borrow().len() >= self.limits.max_in_progress {
      // Stop recursion before we overflow the stack. This mirrors TypeScript's
      // behavior of assuming structural compatibility when the relation engine
      // hits its internal recursion limits.
      let record = record && self.take_reason_slot();
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          true,
          Some("max recursion".into()),
          depth,
        ),
      };
    }

    self.in_progress.borrow_mut().insert(key);

    let outcome = match kind {
      RelationKind::Assignable => self.assignable(src, dst, mode, record, depth),
      RelationKind::Comparable => {
        let src_kind = self.store.type_kind(src);
        let dst_kind = self.store.type_kind(dst);
        if matches!(src_kind, TypeKind::TypeParam(_)) || matches!(dst_kind, TypeKind::TypeParam(_))
        {
          let res = matches!(
            (&src_kind, &dst_kind),
            (TypeKind::TypeParam(a), TypeKind::TypeParam(b)) if a == b
          );
          let record = record && self.take_reason_slot();
          RelationResult {
            result: res,
            reason: self.join_reasons(
              record,
              key,
              Vec::new(),
              res,
              Some("type parameter comparable".into()),
              depth,
            ),
          }
        } else {
          let forward = self.assignable(src, dst, mode, record, depth + 1);
          if !forward.result {
            forward
          } else {
            let backward = self.assignable(dst, src, mode, record, depth + 1);
            let record = record && self.take_reason_slot();
            RelationResult {
              result: backward.result,
              reason: self.join_reasons(
                record,
                key,
                vec![forward.reason, backward.reason],
                backward.result,
                Some("comparable".into()),
                depth,
              ),
            }
          }
        }
      }
      RelationKind::StrictSubtype => {
        let forward = self.assignable(src, dst, mode, record, depth + 1);
        if !forward.result {
          forward
        } else {
          let backward = self.assignable(dst, src, mode, record, depth + 1);
          let res = forward.result && !backward.result;
          let record = record && self.take_reason_slot();
          RelationResult {
            result: res,
            reason: self.join_reasons(
              record,
              key,
              vec![forward.reason, backward.reason],
              res,
              Some("strict subtype".into()),
              depth,
            ),
          }
        }
      }
    };

    self.cache.insert(key, outcome.result);
    self.in_progress.borrow_mut().remove(&key);
    outcome
  }

  fn cached_reason(
    &self,
    record: bool,
    key: RelationKey,
    result: bool,
    depth: usize,
  ) -> Option<ReasonNode> {
    self.join_reasons(
      record,
      key,
      Vec::new(),
      result,
      Some("cached".into()),
      depth,
    )
  }

  fn cycle_reason(&self, record: bool, key: RelationKey, depth: usize) -> Option<ReasonNode> {
    self.join_reasons(record, key, Vec::new(), true, Some("cycle".into()), depth)
  }

  fn join_reasons(
    &self,
    record: bool,
    key: RelationKey,
    children: Vec<Option<ReasonNode>>,
    outcome: bool,
    note: Option<String>,
    depth: usize,
  ) -> Option<ReasonNode> {
    if !record {
      return None;
    }
    let mut note = note;
    let child_nodes = if depth >= MAX_REASON_DEPTH {
      note.get_or_insert_with(|| "max depth".into());
      Vec::new()
    } else {
      children.into_iter().flatten().collect()
    };
    Some(ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome,
      note,
      children: child_nodes,
    })
  }

  fn reset_reason_budget(&self) {
    *self.reason_budget.borrow_mut() = ReasonBudget::default();
  }

  fn take_reason_slot(&self) -> bool {
    let mut budget = self.reason_budget.borrow_mut();
    if budget.nodes >= MAX_REASON_NODES {
      return false;
    }
    budget.nodes += 1;
    true
  }

  fn assignable(
    &self,
    src: TypeId,
    dst: TypeId,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind: RelationKind::Assignable,
      mode,
    };

    if src == dst {
      let record = record && self.take_reason_slot();
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          true,
          Some("identical".into()),
          depth,
        ),
      };
    }

    if let (
      TypeKind::Ref {
        def: src_def,
        args: src_args,
      },
      TypeKind::Ref {
        def: dst_def,
        args: dst_args,
      },
    ) = (self.store.type_kind(src), self.store.type_kind(dst))
    {
      if src_def == dst_def
        && src_args.len() == dst_args.len()
        && !src_args.is_empty()
        && self.hooks.expander.is_some()
      {
        let expander = self.hooks.expander.expect("checked is_some above");
        if let Some(param_decls) = expander.type_param_decls(src_def) {
          if param_decls.len() == src_args.len() {
            let mut saw_variance = false;
            let mut fully_annotated = true;
            let mut children = Vec::new();

            for ((decl, src_arg), dst_arg) in param_decls
              .iter()
              .zip(src_args.iter().copied())
              .zip(dst_args.iter().copied())
            {
              let Some(variance) = decl.variance else {
                fully_annotated = false;
                continue;
              };
              saw_variance = true;
              let record = record && self.take_reason_slot();
              let related = match variance {
                TypeParamVariance::Out => self.relate_internal(
                  src_arg,
                  dst_arg,
                  RelationKind::Assignable,
                  mode,
                  record,
                  depth + 1,
                ),
                TypeParamVariance::In => self.relate_internal(
                  dst_arg,
                  src_arg,
                  RelationKind::Assignable,
                  mode,
                  record,
                  depth + 1,
                ),
                TypeParamVariance::InOut => {
                  let forward = self.relate_internal(
                    src_arg,
                    dst_arg,
                    RelationKind::Assignable,
                    mode,
                    record,
                    depth + 1,
                  );
                  if !forward.result {
                    forward
                  } else {
                    let backward = self.relate_internal(
                      dst_arg,
                      src_arg,
                      RelationKind::Assignable,
                      mode,
                      record,
                      depth + 1,
                    );
                    RelationResult {
                      result: backward.result,
                      reason: self.join_reasons(
                        record,
                        key,
                        vec![forward.reason, backward.reason],
                        backward.result,
                        Some("invariant type argument".into()),
                        depth,
                      ),
                    }
                  }
                }
              };
              if record {
                children.push(related.reason);
              }
              if !related.result {
                let record = record && self.take_reason_slot();
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("variance".into()),
                    depth,
                  ),
                };
              }
            }

            if saw_variance && fully_annotated {
              let record = record && self.take_reason_slot();
              return RelationResult {
                result: true,
                reason: self.join_reasons(
                  record,
                  key,
                  children,
                  true,
                  Some("variance".into()),
                  depth,
                ),
              };
            }
          }
        }
      }
    }

    if !mode.contains(RelationMode::SKIP_NORMALIZE) {
      let normalized_src = self.normalize_type(src);
      let normalized_dst = self.normalize_type(dst);
      if normalized_src != src || normalized_dst != dst {
        let record = record && self.take_reason_slot();
        let related = self.relate_internal(
          normalized_src,
          normalized_dst,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("normalized".into()),
            depth,
          ),
        };
      }
    }

    let src_kind = self.store.type_kind(src);
    let dst_kind = self.store.type_kind(dst);

    if mode.contains(RelationMode::SKIP_NORMALIZE) && depth == 0 {
      debug_assert!(
        !matches!(
          &src_kind,
          TypeKind::Conditional { .. }
            | TypeKind::Mapped(_)
            | TypeKind::IndexedAccess { .. }
            | TypeKind::KeyOf(_)
        ) && !matches!(
          &dst_kind,
          TypeKind::Conditional { .. }
            | TypeKind::Mapped(_)
            | TypeKind::IndexedAccess { .. }
            | TypeKind::KeyOf(_)
        ),
        "SKIP_NORMALIZE assignability expects evaluated types"
      );
    }

    if let Some(res) = self.assignable_special(&src_kind, &dst_kind) {
      let record = record && self.take_reason_slot();
      return RelationResult {
        result: res,
        reason: self.join_reasons(record, key, Vec::new(), res, Some("special".into()), depth),
      };
    }

    if let TypeKind::Ref { def, args } = &src_kind {
      if let Some(expanded) = self.expand_ref(*def, args) {
        if expanded != src {
          let record = record && self.take_reason_slot();
          let related = self.relate_internal(
            expanded,
            dst,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          return RelationResult {
            result: related.result,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              related.result,
              Some("expand src".into()),
              depth,
            ),
          };
        }
      }
    }
    if let TypeKind::Ref { def, args } = &dst_kind {
      if let Some(expanded) = self.expand_ref(*def, args) {
        if expanded != dst {
          let record = record && self.take_reason_slot();
          let related = self.relate_internal(
            src,
            expanded,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          return RelationResult {
            result: related.result,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              related.result,
              Some("expand dst".into()),
              depth,
            ),
          };
        }
      }
    }

    // Conditional types (unevaluated)
    //
    // After normalization (`TypeEvaluator`), unresolved conditional types remain
    // as `TypeKind::Conditional` nodes. They behave like the union of their
    // branch outcomes for assignability checks.
    //
    // Mirror TypeScript's behaviour conservatively:
    // - When the *source* is conditional, ensure both branches flow to `dst`.
    // - When the *target* is conditional, require `src` to be compatible with
    //   both branches.
    if let TypeKind::Conditional {
      true_ty, false_ty, ..
    } = &src_kind
    {
      let record = record && self.take_reason_slot();
      let true_related = self.relate_internal(
        *true_ty,
        dst,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if !record && !true_related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            vec![true_related.reason],
            false,
            Some("conditional source".into()),
            depth,
          ),
        };
      }
      let false_related = self.relate_internal(
        *false_ty,
        dst,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      let res = true_related.result && false_related.result;
      return RelationResult {
        result: res,
        reason: self.join_reasons(
          record,
          key,
          vec![true_related.reason, false_related.reason],
          res,
          Some("conditional source".into()),
          depth,
        ),
      };
    }

    if let TypeKind::Conditional {
      true_ty, false_ty, ..
    } = &dst_kind
    {
      let record = record && self.take_reason_slot();
      let true_related = self.relate_internal(
        src,
        *true_ty,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if !record && !true_related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            vec![true_related.reason],
            false,
            Some("conditional target".into()),
            depth,
          ),
        };
      }
      let false_related = self.relate_internal(
        src,
        *false_ty,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      let res = true_related.result && false_related.result;
      return RelationResult {
        result: res,
        reason: self.join_reasons(
          record,
          key,
          vec![true_related.reason, false_related.reason],
          res,
          Some("conditional target".into()),
          depth,
        ),
      };
    }

    // Unions
    if let TypeKind::Union(srcs) = &src_kind {
      let record = record && self.take_reason_slot();
      let mut children = Vec::new();
      for member in srcs {
        let related = self.relate_internal(
          *member,
          dst,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("union source".into()),
              depth,
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          children,
          true,
          Some("union source".into()),
          depth,
        ),
      };
    }
    if let TypeKind::Union(dsts) = &dst_kind {
      let record = record && self.take_reason_slot();
      let mut attempts = Vec::new();
      for member in dsts {
        let related = self.relate_internal(
          src,
          *member,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        let reason = related.reason;
        if record {
          attempts.push(reason.clone());
        }
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![reason],
              true,
              Some("union target".into()),
              depth,
            ),
          };
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          attempts,
          false,
          Some("union target".into()),
          depth,
        ),
      };
    }

    // Intersections
    if let TypeKind::Intersection(dsts) = &dst_kind {
      let record = record && self.take_reason_slot();
      let mut children = Vec::new();
      for member in dsts {
        let related = self.relate_internal(
          src,
          *member,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("intersection target".into()),
              depth,
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          children,
          true,
          Some("intersection target".into()),
          depth,
        ),
      };
    }

    if let TypeKind::Intersection(srcs) = &src_kind {
      let record = record && self.take_reason_slot();
      if let TypeKind::Object(dst_obj) = &dst_kind {
        if let Some(merged) = self.merge_intersection(srcs) {
          let related = self.relate_object(src, dst, merged, *dst_obj, mode, record, depth + 1);
          return RelationResult {
            result: related.result,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              related.result,
              Some("intersection merge".into()),
              depth,
            ),
          };
        }
      }

      let mut children = Vec::new();
      for member in srcs {
        let related = self.relate_internal(
          *member,
          dst,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              true,
              Some("intersection source".into()),
              depth,
            ),
          };
        }
        if record {
          children.push(related.reason);
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          children,
          false,
          Some("intersection source".into()),
          depth,
        ),
      };
    }

    match (&src_kind, &dst_kind) {
      (TypeKind::BooleanLiteral(a), TypeKind::BooleanLiteral(b)) => {
        let res = a == b;
        let record = record && self.take_reason_slot();
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (TypeKind::NumberLiteral(a), TypeKind::NumberLiteral(b)) => {
        let res = a == b;
        let record = record && self.take_reason_slot();
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (TypeKind::StringLiteral(a), TypeKind::StringLiteral(b)) => {
        let res = a == b;
        let record = record && self.take_reason_slot();
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (TypeKind::BigIntLiteral(a), TypeKind::BigIntLiteral(b)) => {
        let res = a == b;
        let record = record && self.take_reason_slot();
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (
        TypeKind::Array {
          ty: src_elem,
          readonly: src_ro,
        },
        TypeKind::Array {
          ty: dst_elem,
          readonly: dst_ro,
        },
      ) => self.relate_array(
        *src_elem,
        *dst_elem,
        *src_ro,
        *dst_ro,
        key,
        mode,
        record,
        depth + 1,
      ),
      (TypeKind::Array { ty: src_elem, .. }, TypeKind::Object(dst_obj)) => {
        let record = record && self.take_reason_slot();
        let dst_shape = self.store.shape(self.store.object(*dst_obj).shape);
        // `object` (keyword) is represented as an empty structural object type.
        // Arrays (and tuples) are objects in TypeScript, so they are assignable
        // to `object` even though we do not model the full `Array` instance
        // shape here.
        if dst_shape.properties.is_empty()
          && dst_shape.call_signatures.is_empty()
          && dst_shape.construct_signatures.is_empty()
          && dst_shape.indexers.is_empty()
        {
          let reason = self.join_reasons(
            record,
            key,
            Vec::new(),
            true,
            Some("array to empty object".into()),
            depth,
          );
          return RelationResult {
            result: true,
            reason,
          };
        }
        let number_key = self.store.primitive_ids().number;
        if let Some(idx) = dst_shape
          .indexers
          .iter()
          .filter(|idx| self.indexer_key_covers(number_key, idx.key_type, mode, depth))
          .min_by_key(|idx| self.indexer_key_specificity(idx.key_type, mode, depth))
        {
          let related = self.relate_internal(
            *src_elem,
            idx.value_type,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          let reason = self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("array to object indexer".into()),
            depth,
          );
          return RelationResult {
            result: related.result,
            reason,
          };
        }
        RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            false,
            Some("array to object".into()),
            depth,
          ),
        }
      }
      (TypeKind::Tuple(_), TypeKind::Object(dst_obj)) => {
        let record = record && self.take_reason_slot();
        let dst_shape = self.store.shape(self.store.object(*dst_obj).shape);
        let res = dst_shape.properties.is_empty()
          && dst_shape.call_signatures.is_empty()
          && dst_shape.construct_signatures.is_empty()
          && dst_shape.indexers.is_empty();
        RelationResult {
          result: res,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            res,
            Some("tuple to object".into()),
            depth,
          ),
        }
      }
      (TypeKind::Tuple(src_elems), TypeKind::Tuple(dst_elems)) => {
        self.relate_tuple(src_elems, dst_elems, key, mode, record, depth + 1)
      }
      (TypeKind::Array { ty, readonly }, TypeKind::Tuple(dst_elems)) => {
        self.relate_array_to_tuple(*ty, *readonly, dst_elems, key, mode, record, depth + 1)
      }
      (TypeKind::Tuple(src_elems), TypeKind::Array { ty, readonly }) => {
        self.relate_tuple_to_array(src_elems, *ty, *readonly, key, mode, record, depth + 1)
      }
      (TypeKind::Callable { overloads: s }, TypeKind::Callable { overloads: d }) => {
        self.relate_callable(src, dst, s, d, mode, record, depth + 1)
      }
      (TypeKind::Callable { overloads }, TypeKind::Object(obj)) => {
        self.relate_callable_to_object(src, dst, overloads, *obj, key, mode, record, depth + 1)
      }
      (TypeKind::Object(obj), TypeKind::Callable { overloads }) => {
        self.relate_object_to_callable(src, dst, *obj, overloads, key, mode, record, depth + 1)
      }
      (TypeKind::Object(src_obj), TypeKind::Object(dst_obj)) => {
        self.relate_object(src, dst, *src_obj, *dst_obj, mode, record, depth + 1)
      }
      _ => {
        let record = record && self.take_reason_slot();
        RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            false,
            Some("structural".into()),
            depth,
          ),
        }
      }
    }
  }

  fn template_atom_strings(
    &self,
    ty: TypeId,
    depth: usize,
    visited: &mut HashSet<TypeId>,
  ) -> Option<Vec<String>> {
    if depth >= self.limits.max_template_match_depth {
      return None;
    }
    if !visited.insert(ty) {
      // Cyclic template-literal graphs are treated as non-enumerable.
      return None;
    }

    let mut result = match self.store.type_kind(ty) {
      TypeKind::StringLiteral(id) => Some(vec![self.store.name(id)]),
      TypeKind::NumberLiteral(num) => Some(vec![num.0.to_string()]),
      TypeKind::BooleanLiteral(val) => Some(vec![val.to_string()]),
      TypeKind::TemplateLiteral(tpl) => self.template_strings(&tpl, depth + 1, visited),
      TypeKind::Union(members) => {
        let mut out = Vec::new();
        let mut ok = true;
        for member in members {
          let Some(mut vals) = self.template_atom_strings(member, depth + 1, visited) else {
            ok = false;
            break;
          };
          out.append(&mut vals);
          if out.len() > self.limits.max_template_atom_strings {
            ok = false;
            break;
          }
        }
        ok.then_some(out)
      }
      TypeKind::Never => Some(Vec::new()),
      _ => None,
    };

    if let Some(strings) = result.as_mut() {
      strings.sort();
      strings.dedup();
      if strings.len() > self.limits.max_template_atom_strings {
        result = None;
      }
    }

    visited.remove(&ty);
    result
  }

  fn template_strings(
    &self,
    tpl: &crate::TemplateLiteralType,
    depth: usize,
    visited: &mut HashSet<TypeId>,
  ) -> Option<Vec<String>> {
    if depth >= self.limits.max_template_match_depth {
      return None;
    }

    let mut acc = vec![tpl.head.clone()];
    for span in tpl.spans.iter() {
      if acc.is_empty() {
        break;
      }
      let atom_strings = self.template_atom_strings(span.ty, depth + 1, visited)?;
      if atom_strings.is_empty() {
        acc.clear();
        break;
      }
      match acc.len().checked_mul(atom_strings.len()) {
        Some(product) if product <= self.limits.max_template_atom_strings => {}
        _ => return None,
      }
      let mut next = Vec::new();
      for base in &acc {
        for atom in &atom_strings {
          if next.len() >= self.limits.max_template_atom_strings {
            return None;
          }
          let mut new = base.clone();
          new.push_str(atom);
          new.push_str(&span.literal);
          next.push(new);
        }
      }
      acc = next;
    }
    if acc.len() > self.limits.max_template_atom_strings {
      return None;
    }
    acc.sort();
    acc.dedup();
    Some(acc)
  }

  fn string_matches_template(
    &self,
    value: &str,
    tpl: &crate::TemplateLiteralType,
    depth: usize,
  ) -> bool {
    if depth >= self.limits.max_template_match_depth {
      return false;
    }

    if !value.starts_with(&tpl.head) {
      return false;
    }

    let mut span_atoms: Vec<Option<Vec<String>>> = Vec::with_capacity(tpl.spans.len());
    for span in tpl.spans.iter() {
      let mut visited = HashSet::new();
      span_atoms.push(self.template_atom_strings(span.ty, depth + 1, &mut visited));
    }

    let mut queue = VecDeque::new();
    queue.push_back((0usize, tpl.head.len()));

    let mut seen = HashSet::new();
    let mut processed = 0usize;

    while let Some((idx, pos)) = queue.pop_front() {
      if !seen.insert((idx, pos)) {
        continue;
      }
      processed += 1;
      if processed > self.limits.max_template_match_states {
        return false;
      }

      if idx == tpl.spans.len() {
        if pos == value.len() {
          return true;
        }
        continue;
      }

      let span = &tpl.spans[idx];
      let Some(remainder) = value.get(pos..) else {
        continue;
      };

      match &span_atoms[idx] {
        Some(atoms) => {
          for atom in atoms {
            if !remainder.starts_with(atom) {
              continue;
            }
            let after_atom = pos + atom.len();
            let Some(after_atom_str) = value.get(after_atom..) else {
              continue;
            };
            if !after_atom_str.starts_with(&span.literal) {
              continue;
            }
            queue.push_back((idx + 1, after_atom + span.literal.len()));
          }
        }
        None => {
          if span.literal.is_empty() {
            queue.push_back((idx + 1, pos));
            for (off, _) in remainder.char_indices().skip(1) {
              if processed + queue.len() >= self.limits.max_template_match_states {
                break;
              }
              queue.push_back((idx + 1, pos + off));
            }
            queue.push_back((idx + 1, value.len()));
          } else {
            let mut search_pos = pos;
            while search_pos <= value.len() {
              let Some(search_slice) = value.get(search_pos..) else {
                break;
              };
              let Some(found_rel) = search_slice.find(&span.literal) else {
                break;
              };
              let found = search_pos + found_rel;
              queue.push_back((idx + 1, found + span.literal.len()));
              if processed + queue.len() >= self.limits.max_template_match_states {
                break;
              }
              let Some(ch) = value.get(found..).and_then(|s| s.chars().next()) else {
                break;
              };
              search_pos = found + ch.len_utf8();
            }
          }
        }
      }
    }

    false
  }

  fn assignable_special(&self, src: &TypeKind, dst: &TypeKind) -> Option<bool> {
    let opts = &self.options;
    if !opts.strict_null_checks
      && (matches!(src, TypeKind::Null | TypeKind::Undefined)
        || matches!(dst, TypeKind::Null | TypeKind::Undefined))
    {
      return Some(true);
    }

    let is_string_mapping_intrinsic = |kind: IntrinsicKind| {
      matches!(
        kind,
        IntrinsicKind::Uppercase
          | IntrinsicKind::Lowercase
          | IntrinsicKind::Capitalize
          | IntrinsicKind::Uncapitalize
      )
    };

    match (src, dst) {
      (TypeKind::TypeParam(a), TypeKind::TypeParam(b)) => Some(a == b),
      // Unresolved type parameters are treated conservatively as `unknown` to
      // avoid spurious incompatibilities during overload checking. They accept
      // any source but are only assignable to top types when used as sources.
      (_, TypeKind::TypeParam(_)) => Some(true),
      (TypeKind::TypeParam(_), _) => Some(matches!(dst, TypeKind::Any | TypeKind::Unknown)),
      // `NoInfer<T>` is transparent for assignability. The evaluator usually
      // erases `NoInfer`, but keep this shortcut for SKIP_NORMALIZE checks.
      (
        TypeKind::Intrinsic {
          kind: IntrinsicKind::NoInfer,
          ty,
        },
        _,
      ) => self.assignable_special(&self.store.type_kind(*ty), dst),
      (
        _,
        TypeKind::Intrinsic {
          kind: IntrinsicKind::NoInfer,
          ty,
        },
      ) => self.assignable_special(src, &self.store.type_kind(*ty)),
      // `BuiltinIteratorReturn` behaves like `any` in TypeScript.
      (
        TypeKind::Intrinsic {
          kind: IntrinsicKind::BuiltinIteratorReturn,
          ..
        },
        _,
      )
      | (
        _,
        TypeKind::Intrinsic {
          kind: IntrinsicKind::BuiltinIteratorReturn,
          ..
        },
      ) => Some(true),
      // String-mapping intrinsics (Uppercase/Lowercase/Capitalize/Uncapitalize)
      // are always string-like. When used as destinations, treat them like
      // `string` (accept only string-like sources).
      (TypeKind::Intrinsic { kind, .. }, TypeKind::String)
        if is_string_mapping_intrinsic(*kind) =>
      {
        Some(true)
      }
      (src, TypeKind::Intrinsic { kind, .. }) if is_string_mapping_intrinsic(*kind) => match src {
        // Preserve the meaning of `any` and `never`, which are handled below.
        TypeKind::Any | TypeKind::Never => None,
        TypeKind::String | TypeKind::StringLiteral(_) | TypeKind::TemplateLiteral(_) => Some(true),
        TypeKind::Intrinsic { kind: src_kind, .. } if is_string_mapping_intrinsic(*src_kind) => {
          Some(true)
        }
        // Defer composite types to the structural relation engine so it can
        // distribute unions/intersections and expand references.
        TypeKind::Union(_)
        | TypeKind::Intersection(_)
        | TypeKind::Ref { .. }
        | TypeKind::IndexedAccess { .. }
        | TypeKind::Conditional { .. }
        | TypeKind::Mapped(_)
        | TypeKind::KeyOf(_) => None,
        _ => Some(false),
      },
      (TypeKind::Any, _) | (_, TypeKind::Any) => Some(true),
      (TypeKind::Unknown, TypeKind::Unknown) => Some(true),
      (_, TypeKind::Unknown) => Some(true),
      (TypeKind::Unknown, _) => Some(false),
      (TypeKind::EmptyObject, _) => Some(matches!(
        dst,
        TypeKind::Any | TypeKind::Unknown | TypeKind::EmptyObject
      )),
      (TypeKind::Never, _) => Some(true),
      (_, TypeKind::Never) => Some(matches!(src, TypeKind::Never)),
      (TypeKind::Void, TypeKind::Void) => Some(true),
      (TypeKind::Void, TypeKind::Undefined) | (TypeKind::Undefined, TypeKind::Void) => Some(true),
      (TypeKind::Void, TypeKind::EmptyObject) => Some(!opts.strict_null_checks),
      (
        TypeKind::Void,
        TypeKind::Union(_)
        | TypeKind::Intersection(_)
        | TypeKind::Ref { .. }
        | TypeKind::IndexedAccess { .. }
        | TypeKind::Conditional { .. }
        | TypeKind::Mapped(_)
        | TypeKind::KeyOf(_),
      ) => None,
      (TypeKind::Void, _) => Some(false),
      (_, TypeKind::EmptyObject) => {
        if !opts.strict_null_checks {
          Some(true)
        } else {
          Some(!matches!(src, TypeKind::Null | TypeKind::Undefined))
        }
      }
      (TypeKind::Null, TypeKind::Null) => Some(true),
      (TypeKind::Undefined, TypeKind::Undefined) => Some(true),
      (
        TypeKind::Null | TypeKind::Undefined,
        TypeKind::Union(_)
        | TypeKind::Intersection(_)
        | TypeKind::Ref { .. }
        | TypeKind::IndexedAccess { .. }
        | TypeKind::Conditional { .. }
        | TypeKind::Mapped(_)
        | TypeKind::KeyOf(_),
      ) => None,
      (
        TypeKind::Union(_)
        | TypeKind::Intersection(_)
        | TypeKind::Ref { .. }
        | TypeKind::IndexedAccess { .. }
        | TypeKind::Conditional { .. }
        | TypeKind::Mapped(_)
        | TypeKind::KeyOf(_),
        TypeKind::Null | TypeKind::Undefined,
      ) => None,
      (TypeKind::Null | TypeKind::Undefined, _) | (_, TypeKind::Null | TypeKind::Undefined) => {
        Some(false)
      }
      (TypeKind::BooleanLiteral(_), TypeKind::Boolean) => Some(true),
      (TypeKind::NumberLiteral(_), TypeKind::Number) => Some(true),
      (TypeKind::StringLiteral(_), TypeKind::String) => Some(true),
      (TypeKind::BigIntLiteral(_), TypeKind::BigInt) => Some(true),
      (TypeKind::StringLiteral(src), TypeKind::TemplateLiteral(dst_tpl)) => {
        let value = self.store.name(*src);
        Some(self.string_matches_template(&value, dst_tpl, 0))
      }
      (TypeKind::TemplateLiteral(src_tpl), TypeKind::TemplateLiteral(dst_tpl)) => {
        let mut visited = HashSet::new();
        match self.template_strings(src_tpl, 0, &mut visited) {
          Some(src_strings) => Some(
            src_strings
              .iter()
              .all(|s| self.string_matches_template(s, dst_tpl, 0)),
          ),
          None => {
            // Non-enumerable template literal types can contain infinitely many
            // strings. We do not currently attempt to prove template-to-template
            // assignability for those patterns, so only identical TypeIds
            // (handled earlier) are accepted.
            Some(false)
          }
        }
      }
      (TypeKind::TemplateLiteral(_), TypeKind::String) => Some(true),
      (TypeKind::UniqueSymbol, TypeKind::Symbol) => Some(true),
      (TypeKind::Predicate { .. }, TypeKind::Boolean) => Some(true),
      (TypeKind::Boolean, TypeKind::Predicate { .. }) => Some(true),
      (TypeKind::Predicate { .. }, TypeKind::Predicate { .. }) => Some(true),
      _ => None,
    }
  }

  fn relate_array(
    &self,
    src_elem: TypeId,
    dst_elem: TypeId,
    src_readonly: bool,
    dst_readonly: bool,
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    if !dst_readonly && src_readonly {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("readonly array".into()),
          depth,
        ),
      };
    }
    let related = self.relate_internal(
      src_elem,
      dst_elem,
      RelationKind::Assignable,
      mode,
      record,
      depth + 1,
    );
    RelationResult {
      result: related.result,
      reason: self.join_reasons(
        record,
        key,
        vec![related.reason],
        related.result,
        Some("array element".into()),
        depth,
      ),
    }
  }

  fn relate_array_to_tuple(
    &self,
    src_elem: TypeId,
    src_readonly: bool,
    dst_elems: &[crate::TupleElem],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    // Array -> fixed tuple is not assignable because an array type cannot
    // statically guarantee the tuple's maximum length.
    //
    // Arrays can be assignable to variadic tuples (those containing a rest
    // element), but TypeScript's semantics for those are intentionally loose.
    let dst_readonly = dst_elems.iter().all(|e| e.readonly);
    if src_readonly && !dst_readonly {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("readonly array".into()),
          depth,
        ),
      };
    }

    let has_rest = dst_elems.iter().any(|e| e.rest);
    if !has_rest {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("array to fixed tuple".into()),
          depth,
        ),
      };
    }

    // If the tuple is purely a spread (`[...T]`), treat it as array-like and
    // compare element types against the spread element type.
    if dst_elems.iter().all(|e| e.rest) {
      let rest = dst_elems
        .iter()
        .find(|e| e.rest)
        .expect("has_rest implies at least one rest element");
      let spread_elem = self.spread_element_type(rest.ty);
      let related = self.relate_internal(
        src_elem,
        spread_elem,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      return RelationResult {
        result: related.result,
        reason: self.join_reasons(
          record,
          key,
          vec![related.reason],
          related.result,
          Some("array to rest tuple".into()),
          depth,
        ),
      };
    }

    // Arrays do not satisfy required tuple positions, but they can flow into
    // optional elements before the rest portion.
    if dst_elems.iter().any(|e| !e.rest && !e.optional) {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("array required tuple element".into()),
          depth,
        ),
      };
    }

    let mut children = Vec::new();
    for dst_elem in dst_elems.iter().filter(|e| !e.rest) {
      let dst_ty = self.optional_type(dst_elem.ty, dst_elem.optional, OptionalFlavor::TupleElement);
      let related = self.relate_internal(
        src_elem,
        dst_ty,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("array to variadic tuple".into()),
            depth,
          ),
        };
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(
        record,
        key,
        children,
        true,
        Some("array to variadic tuple".into()),
        depth,
      ),
    }
  }

  /// Extract the element type produced by spreading `ty`.
  ///
  /// This mirrors TypeScript's behavior for spreads in rest-parameter positions:
  /// - arrays contribute their element type
  /// - tuples contribute the union of their element types (including nested spreads)
  /// - unions/intersections are distributed
  /// - `TypeKind::Ref` is expanded via the configured [`RelateTypeExpander`] hook
  ///
  /// The result is intended for inference/call-checking helpers that need to
  /// reason about `...expr` without re-implementing spread flattening logic.
  pub fn spread_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut queue = vec![ty];
    let mut seen = HashSet::new();
    let mut out = Vec::new();

    while let Some(next) = queue.pop() {
      if !seen.insert(next) {
        continue;
      }
      match self.store.type_kind(next) {
        TypeKind::Array { ty, .. } => out.push(ty),
        TypeKind::Tuple(elems) => {
          for elem in elems {
            if elem.rest {
              queue.push(elem.ty);
            } else {
              out.push(self.optional_type(elem.ty, elem.optional, OptionalFlavor::TupleElement));
            }
          }
        }
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for member in members {
            queue.push(member);
          }
        }
        TypeKind::Ref { def, args } => {
          if let Some(expanded) = self.expand_ref(def, &args) {
            queue.push(expanded);
          } else {
            out.push(prim.unknown);
          }
        }
        _ => out.push(prim.unknown),
      }
    }

    if out.is_empty() {
      prim.unknown
    } else if out.len() == 1 {
      out[0]
    } else {
      self.store.union(out)
    }
  }

  fn relate_tuple_to_array(
    &self,
    src_elems: &[crate::TupleElem],
    dst_elem: TypeId,
    dst_readonly: bool,
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    if !dst_readonly && src_elems.iter().any(|e| e.readonly) {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("tuple readonly element".into()),
          depth,
        ),
      };
    }
    let mut children = Vec::new();
    for src_elem in src_elems {
      let src_ty = if src_elem.rest {
        let spread_elem = self.spread_element_type(src_elem.ty);
        self.optional_type(spread_elem, src_elem.optional, OptionalFlavor::TupleElement)
      } else {
        self.optional_type(src_elem.ty, src_elem.optional, OptionalFlavor::TupleElement)
      };
      let related = self.relate_internal(
        src_ty,
        dst_elem,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("tuple to array".into()),
            depth,
          ),
        };
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(
        record,
        key,
        children,
        true,
        Some("tuple to array".into()),
        depth,
      ),
    }
  }

  fn relate_tuple(
    &self,
    src_elems: &[crate::TupleElem],
    dst_elems: &[crate::TupleElem],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    let mut children = Vec::new();
    let src_required = src_elems.iter().filter(|e| !e.optional && !e.rest).count();
    let dst_required = dst_elems.iter().filter(|e| !e.optional && !e.rest).count();

    if src_required > dst_elems.len()
      && !src_elems.iter().any(|e| e.rest)
      && dst_required == dst_elems.len()
    {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("tuple arity".into()),
          depth,
        ),
      };
    }

    if dst_required > src_elems.len() && !src_elems.iter().any(|e| e.rest) {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("tuple required elements".into()),
          depth,
        ),
      };
    }

    let mut s_idx = 0usize;
    let mut d_idx = 0usize;
    while d_idx < dst_elems.len() {
      let dst_elem = &dst_elems[d_idx];
      let src_elem = src_elems.get(s_idx);
      match src_elem {
        None => {
          if dst_elem.rest || dst_elem.optional {
            d_idx += 1;
            continue;
          }
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("tuple length".into()),
              depth,
            ),
          };
        }
        Some(src_elem) => {
          if dst_elem.rest {
            for rem in src_elems.iter().skip(s_idx) {
              let src_ty = self.optional_type(
                rem.ty,
                rem.optional || rem.rest,
                OptionalFlavor::TupleElement,
              );
              let dst_ty = self.optional_type(
                dst_elem.ty,
                dst_elem.optional || dst_elem.rest,
                OptionalFlavor::TupleElement,
              );
              if !dst_elem.readonly && rem.readonly {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple readonly".into()),
                    depth,
                  ),
                };
              }
              let related = self.relate_internal(
                src_ty,
                dst_ty,
                RelationKind::Assignable,
                mode,
                record,
                depth + 1,
              );
              if record {
                children.push(related.reason);
              }
              if !related.result {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple rest".into()),
                    depth,
                  ),
                };
              }
            }
            return RelationResult {
              result: true,
              reason: self.join_reasons(
                record,
                key,
                children,
                true,
                Some("tuple rest".into()),
                depth,
              ),
            };
          }

          if src_elem.rest {
            let src_ty = self.optional_type(
              src_elem.ty,
              src_elem.optional || src_elem.rest,
              OptionalFlavor::TupleElement,
            );
            for d in dst_elems.iter().skip(d_idx) {
              if !d.readonly && src_elem.readonly {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple rest readonly".into()),
                    depth,
                  ),
                };
              }
              let dst_ty =
                self.optional_type(d.ty, d.optional || d.rest, OptionalFlavor::TupleElement);
              let related = self.relate_internal(
                src_ty,
                dst_ty,
                RelationKind::Assignable,
                mode,
                record,
                depth + 1,
              );
              if record {
                children.push(related.reason);
              }
              if !related.result {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple rest spread".into()),
                    depth,
                  ),
                };
              }
            }
            return RelationResult {
              result: true,
              reason: self.join_reasons(
                record,
                key,
                children,
                true,
                Some("tuple rest spread".into()),
                depth,
              ),
            };
          }

          if !dst_elem.optional && src_elem.optional {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("tuple optional".into()),
                depth,
              ),
            };
          }
          if !dst_elem.readonly && src_elem.readonly {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("tuple readonly".into()),
                depth,
              ),
            };
          }
          let src_ty =
            self.optional_type(src_elem.ty, src_elem.optional, OptionalFlavor::TupleElement);
          let dst_ty =
            self.optional_type(dst_elem.ty, dst_elem.optional, OptionalFlavor::TupleElement);
          let related = self.relate_internal(
            src_ty,
            dst_ty,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("tuple element".into()),
                depth,
              ),
            };
          }
        }
      }

      s_idx += 1;
      d_idx += 1;
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("tuple".into()), depth),
    }
  }

  fn relate_callable(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_overloads: &[SignatureId],
    dst_overloads: &[SignatureId],
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let record = record && self.take_reason_slot();
    let mut children = Vec::new();
    for dst_sig in dst_overloads {
      let dst_sig_data = self.store.signature(*dst_sig);
      let mut matched = None;
      for src_sig in src_overloads {
        let src_sig_data = self.store.signature(*src_sig);
        let related = self.relate_signature(
          *src_sig,
          *dst_sig,
          &src_sig_data,
          &dst_sig_data,
          mode,
          record,
          depth + 1,
        );
        if related.result {
          matched = Some(related.reason);
          break;
        }
        if record {
          children.push(related.reason);
        }
      }
      if matched.is_none() {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("call signature".into()),
            depth,
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("callable".into()), depth),
    }
  }

  fn relate_callable_to_object(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    overloads: &[SignatureId],
    dst_obj: ObjectId,
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    let dst_shape = self.store.shape(self.store.object(dst_obj).shape);
    if !dst_shape.properties.is_empty()
      || !dst_shape.construct_signatures.is_empty()
      || !dst_shape.indexers.is_empty()
    {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("callable to object".into()),
          depth,
        ),
      };
    }
    self.relate_callable(
      src_id,
      dst_id,
      overloads,
      &dst_shape.call_signatures,
      mode | RelationMode::BIVARIANT_PARAMS,
      record,
      depth + 1,
    )
  }

  fn relate_object_to_callable(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_obj: ObjectId,
    overloads: &[SignatureId],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    let src_shape = self.store.shape(self.store.object(src_obj).shape);
    if !src_shape.properties.is_empty()
      || !src_shape.construct_signatures.is_empty()
      || !src_shape.indexers.is_empty()
    {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("object to callable".into()),
          depth,
        ),
      };
    }
    self.relate_callable(
      src_id,
      dst_id,
      &src_shape.call_signatures,
      overloads,
      mode | RelationMode::BIVARIANT_PARAMS,
      record,
      depth + 1,
    )
  }

  fn relate_signature(
    &self,
    src_id: SignatureId,
    dst_id: SignatureId,
    src: &Signature,
    dst: &Signature,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let record = record && self.take_reason_slot();
    let (src_reason_ty, dst_reason_ty) = if record {
      (
        self.store.intern_type(TypeKind::Callable {
          overloads: vec![src_id],
        }),
        self.store.intern_type(TypeKind::Callable {
          overloads: vec![dst_id],
        }),
      )
    } else {
      (TypeId(src_id.0), TypeId(dst_id.0))
    };
    let key = RelationKey {
      src: src_reason_ty,
      dst: dst_reason_ty,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children = Vec::new();
    let allow_bivariance =
      !self.options.strict_function_types || mode.contains(RelationMode::BIVARIANT_PARAMS);

    if src.type_params.len() != dst.type_params.len() {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("type parameters".into()),
          depth,
        ),
      };
    }

    match (&src.this_param, &dst.this_param) {
      (Some(s), Some(d)) => {
        let related =
          self.relate_internal(*d, *s, RelationKind::Assignable, mode, record, depth + 1);
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("this parameter".into()),
              depth,
            ),
          };
        }
      }
      (Some(_), None) => {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("this parameter".into()),
            depth,
          ),
        }
      }
      (None, Some(d)) => {
        // A signature without an explicit `this` parameter is effectively
        // `this: any` in TypeScript. This is important for callback-heavy DOM
        // APIs where the expected type includes a `this` parameter but common
        // call sites (arrow functions) omit it.
        let any_this = self.store.primitive_ids().any;
        let related = self.relate_internal(
          *d,
          any_this,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("this parameter".into()),
              depth,
            ),
          };
        }
      }
      _ => {}
    }

    let src_required = src.params.iter().filter(|p| !p.optional && !p.rest).count();
    let dst_required = dst.params.iter().filter(|p| !p.optional && !p.rest).count();
    if src_required > dst_required {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("parameter count".into()),
          depth,
        ),
      };
    }

    let prim = self.store.primitive_ids();
    let src_rest_index = src.params.iter().position(|p| p.rest);
    let dst_rest_index = dst.params.iter().position(|p| p.rest);

    let effective_param_type =
      |sig: &Signature, rest_index: Option<usize>, index: usize| match sig.params.get(index) {
        Some(param) => {
          let ty = if param.rest {
            self.spread_element_type(param.ty)
          } else {
            param.ty
          };
          self.optional_type(ty, param.optional, OptionalFlavor::Parameter)
        }
        None => match rest_index {
          Some(rest_index) if index >= rest_index => sig
            .params
            .get(rest_index)
            .map(|rest_param| {
              let spread_elem = self.spread_element_type(rest_param.ty);
              self.optional_type(spread_elem, rest_param.optional, OptionalFlavor::Parameter)
            })
            .unwrap_or(prim.any),
          _ => prim.any,
        },
      };

    for index in 0..src.params.len().max(dst.params.len()) {
      // If the destination signature has no parameter here and no rest parameter
      // either, it can never be called with an argument at this position.
      if index >= dst.params.len() && dst_rest_index.is_none() {
        break;
      }

      let s_ty = effective_param_type(src, src_rest_index, index);
      let d_ty = effective_param_type(dst, dst_rest_index, index);

      let related = if allow_bivariance {
        let forward = self.relate_internal(
          s_ty,
          d_ty,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if forward.result {
          forward
        } else {
          self.relate_internal(
            d_ty,
            s_ty,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          )
        }
      } else {
        self.relate_internal(
          d_ty,
          s_ty,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        )
      };

      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("parameter".into()),
            depth,
          ),
        };
      }
    }

    // TypeScript treats `void` return types as non-observable at the call site:
    // a function that returns a value is still assignable to a `() => void`
    // callback since callers ignore the return value.
    if !matches!(self.store.type_kind(dst.ret), TypeKind::Void) {
      let ret_related = self.relate_internal(
        src.ret,
        dst.ret,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if record {
        children.push(ret_related.reason);
      }
      if !ret_related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("return".into()), depth),
        };
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("signature".into()), depth),
    }
  }

  fn merge_intersection(&self, members: &[TypeId]) -> Option<ObjectId> {
    let mut shape = Shape::new();
    for member in members {
      match self.store.type_kind(*member) {
        TypeKind::Object(obj) => {
          let obj = self.store.object(obj);
          let obj_shape = self.store.shape(obj.shape);
          shape.properties.extend(obj_shape.properties.clone());
          shape.indexers.extend(obj_shape.indexers.clone());
          shape
            .call_signatures
            .extend(obj_shape.call_signatures.clone());
          shape
            .construct_signatures
            .extend(obj_shape.construct_signatures.clone());
        }
        _ => return None,
      }
    }
    let shape_id = self.store.intern_shape(shape);
    Some(
      self
        .store
        .intern_object(crate::ObjectType { shape: shape_id }),
    )
  }

  fn optional_type(&self, ty: TypeId, optional: bool, flavor: OptionalFlavor) -> TypeId {
    if !optional && !matches!(flavor, OptionalFlavor::IndexerValue) {
      return ty;
    }

    let include_undefined = match flavor {
      OptionalFlavor::Property => !self.options.exact_optional_property_types && optional,
      OptionalFlavor::Parameter | OptionalFlavor::TupleElement => optional,
      OptionalFlavor::IndexerValue => optional || self.options.no_unchecked_indexed_access,
    };

    if include_undefined {
      self
        .store
        .union(vec![ty, self.store.primitive_ids().undefined])
    } else {
      ty
    }
  }

  fn normalize_type(&self, ty: TypeId) -> TypeId {
    #[cfg(test)]
    {
      NORMALIZE_CALLS.with(|counter| counter.set(counter.get() + 1));
    }

    #[cfg(feature = "tracing")]
    let before_stats = self.normalizer_caches.stats();
    #[cfg(feature = "tracing")]
    let span = tracing::trace_span!(
      "types_ts_interned::RelateCtx::normalize_type",
      ty = ?ty,
      eval_cache_hits = tracing::field::Empty,
      eval_cache_misses = tracing::field::Empty,
      ref_cache_hits = tracing::field::Empty,
      ref_cache_misses = tracing::field::Empty,
      result = tracing::field::Empty,
    );
    #[cfg(feature = "tracing")]
    let _enter = span.enter();

    let adapter = RelateExpanderAdapter {
      hook: self.hooks.expander,
    };
    let mut evaluator =
      TypeEvaluator::with_caches(self.store.clone(), &adapter, self.normalizer_caches.clone())
        .with_step_limit(self.limits.step_limit)
        .with_conditional_assignability(self);
    let result = evaluator.evaluate(ty);

    #[cfg(feature = "tracing")]
    {
      let after_stats = self.normalizer_caches.stats();
      let eval_delta = cache_stats_delta(before_stats.eval, after_stats.eval);
      let refs_delta = cache_stats_delta(before_stats.references, after_stats.references);
      span.record("eval_cache_hits", &eval_delta.hits);
      span.record("eval_cache_misses", &eval_delta.misses);
      span.record("ref_cache_hits", &refs_delta.hits);
      span.record("ref_cache_misses", &refs_delta.misses);
      span.record("result", &tracing::field::debug(&result));
    }

    result
  }

  fn is_method_like(&self, data: &PropData) -> bool {
    data.is_method
  }

  fn relate_object(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_obj: ObjectId,
    dst_obj: ObjectId,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let record = record && self.take_reason_slot();
    let mut children: Vec<Option<ReasonNode>> = Vec::new();

    let src_shape = self.store.shape(self.store.object(src_obj).shape);
    let dst_shape = self.store.shape(self.store.object(dst_obj).shape);

    for dst_prop in &dst_shape.properties {
      match self.find_property(&src_shape, &dst_prop.key) {
        Some(src_prop) => {
          if !self.private_compatible(src_prop, dst_prop) {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("private/protected property".into()),
                depth,
              ),
            };
          }
          if !dst_prop.data.readonly && src_prop.data.readonly {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("readonly property".into()),
                depth,
              ),
            };
          }

          if !dst_prop.data.optional && src_prop.data.optional {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("missing required property".into()),
                depth,
              ),
            };
          }

          let next_mode =
            if self.is_method_like(&src_prop.data) || self.is_method_like(&dst_prop.data) {
              mode | RelationMode::BIVARIANT_PARAMS
            } else {
              mode
            };
          let src_ty = self.optional_type(
            src_prop.data.ty,
            src_prop.data.optional,
            OptionalFlavor::Property,
          );
          let dst_ty = self.optional_type(
            dst_prop.data.ty,
            dst_prop.data.optional,
            OptionalFlavor::Property,
          );
          let related = self.relate_internal(
            src_ty,
            dst_ty,
            RelationKind::Assignable,
            next_mode,
            record,
            depth + 1,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("property type".into()),
                depth,
              ),
            };
          }
        }
        None => {
          if dst_prop.data.optional {
            continue;
          }
          if let Some(index) = self.indexer_for_prop(&src_shape, &dst_prop.key, mode, depth + 1) {
            if !dst_prop.data.readonly && index.readonly {
              return RelationResult {
                result: false,
                reason: self.join_reasons(
                  record,
                  key,
                  children,
                  false,
                  Some("indexer readonly".into()),
                  depth,
                ),
              };
            }
            let related = self.relate_internal(
              self.optional_type(index.value_type, false, OptionalFlavor::IndexerValue),
              self.optional_type(
                dst_prop.data.ty,
                dst_prop.data.optional,
                OptionalFlavor::Property,
              ),
              RelationKind::Assignable,
              mode,
              record,
              depth + 1,
            );
            if record {
              children.push(related.reason);
            }
            if !related.result {
              return RelationResult {
                result: false,
                reason: self.join_reasons(
                  record,
                  key,
                  children,
                  false,
                  Some("indexer property".into()),
                  depth,
                ),
              };
            }
          } else {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("missing property".into()),
                depth,
              ),
            };
          }
        }
      }
    }

    for dst_index in &dst_shape.indexers {
      if let Some(src_idx) =
        self.find_matching_indexer(&src_shape, dst_index, mode, record, depth + 1)
      {
        if !dst_index.readonly && src_idx.readonly {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("readonly indexer".into()),
              depth,
            ),
          };
        }
        let related = self.relate_internal(
          self.optional_type(src_idx.value_type, false, OptionalFlavor::IndexerValue),
          self.optional_type(dst_index.value_type, false, OptionalFlavor::IndexerValue),
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(record, key, children, false, Some("indexer".into()), depth),
          };
        }
      } else if src_shape.indexers.is_empty() {
        for prop in &src_shape.properties {
          if !self.indexer_accepts_prop(dst_index, &prop.key, mode, depth + 1) {
            continue;
          }
          let related = self.relate_internal(
            self.optional_type(prop.data.ty, prop.data.optional, OptionalFlavor::Property),
            self.optional_type(dst_index.value_type, false, OptionalFlavor::IndexerValue),
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("property vs indexer".into()),
                depth,
              ),
            };
          }
        }
      } else {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("missing indexer".into()),
            depth,
          ),
        };
      }
    }

    for dst_sig in &dst_shape.call_signatures {
      let dst_sig_data = self.store.signature(*dst_sig);
      let mut matched = None;
      for src_sig in &src_shape.call_signatures {
        let src_sig_data = self.store.signature(*src_sig);
        let related = self.relate_signature(
          *src_sig,
          *dst_sig,
          &src_sig_data,
          &dst_sig_data,
          mode | RelationMode::BIVARIANT_PARAMS,
          record,
          depth + 1,
        );
        if related.result {
          matched = Some(related.reason);
          break;
        }
        if record {
          children.push(related.reason);
        }
      }
      if matched.is_none() {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("call signature".into()),
            depth,
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }

    for dst_sig in &dst_shape.construct_signatures {
      let dst_sig_data = self.store.signature(*dst_sig);
      let mut matched = None;
      for src_sig in &src_shape.construct_signatures {
        let src_sig_data = self.store.signature(*src_sig);
        let related = self.relate_signature(
          *src_sig,
          *dst_sig,
          &src_sig_data,
          &dst_sig_data,
          mode | RelationMode::BIVARIANT_PARAMS,
          record,
          depth + 1,
        );
        if related.result {
          matched = Some(related.reason);
          break;
        }
        if record {
          children.push(related.reason);
        }
      }
      if matched.is_none() {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("construct signature".into()),
            depth,
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("object".into()), depth),
    }
  }

  fn private_compatible(&self, src: &Property, dst: &Property) -> bool {
    let src_access = src
      .data
      .accessibility
      .as_ref()
      .cloned()
      .unwrap_or(Accessibility::Public);
    let dst_access = dst
      .data
      .accessibility
      .as_ref()
      .cloned()
      .unwrap_or(Accessibility::Public);
    match (src_access, dst_access) {
      (Accessibility::Public, Accessibility::Public) => true,
      (Accessibility::Public, _) | (_, Accessibility::Public) => false,
      (a, b) if a != b => false,
      _ => {
        if let Some(cb) = self.hooks.is_same_origin_private_member {
          return cb(src, dst);
        }
        match (src.data.declared_on, dst.data.declared_on) {
          (Some(left), Some(right)) if left == right => true,
          _ => match (src.data.origin, dst.data.origin) {
            (Some(left), Some(right)) => left == right,
            _ => false,
          },
        }
      }
    }
  }

  fn indexer_for_prop<'b>(
    &self,
    shape: &'b Shape,
    name: &PropKey,
    mode: RelationMode,
    depth: usize,
  ) -> Option<&'b Indexer> {
    let mut key_kind = self.prop_key_kind(name);
    if matches!(key_kind, PropKeyKind::String)
      && parse_canonical_index_string(self.store.as_ref(), name).is_some()
    {
      key_kind = PropKeyKind::Number;
    }
    shape
      .indexers
      .iter()
      .filter(|idx| self.indexer_key_accepts_prop_kind(idx.key_type, key_kind, mode, depth))
      .min_by_key(|idx| self.indexer_key_specificity(idx.key_type, mode, depth))
  }

  fn indexer_accepts_prop(
    &self,
    idx: &Indexer,
    key: &PropKey,
    mode: RelationMode,
    depth: usize,
  ) -> bool {
    let mut key_kind = self.prop_key_kind(key);
    if matches!(key_kind, PropKeyKind::String)
      && parse_canonical_index_string(self.store.as_ref(), key).is_some()
    {
      key_kind = PropKeyKind::Number;
    }
    self.indexer_key_accepts_prop_kind(idx.key_type, key_kind, mode, depth)
  }

  fn find_matching_indexer<'b>(
    &self,
    shape: &'b Shape,
    dst: &Indexer,
    mode: RelationMode,
    _record: bool,
    depth: usize,
  ) -> Option<&'b Indexer> {
    shape
      .indexers
      .iter()
      .filter(|src_idx| self.indexer_key_covers(src_idx.key_type, dst.key_type, mode, depth))
      .min_by_key(|src_idx| self.indexer_key_specificity(src_idx.key_type, mode, depth))
  }

  fn indexer_key_covers(
    &self,
    src_key: TypeId,
    dst_key: TypeId,
    mode: RelationMode,
    depth: usize,
  ) -> bool {
    use PropKeyKind::*;
    [String, Number, Symbol].into_iter().all(|kind| {
      !self.indexer_key_accepts_prop_kind(dst_key, kind, mode, depth)
        || self.indexer_key_accepts_prop_kind(src_key, kind, mode, depth)
    })
  }

  fn indexer_key_specificity(&self, idx_key: TypeId, mode: RelationMode, depth: usize) -> u8 {
    use PropKeyKind::*;
    [String, Number, Symbol]
      .into_iter()
      .filter(|kind| self.indexer_key_accepts_prop_kind(idx_key, *kind, mode, depth))
      .count() as u8
  }

  fn indexer_key_accepts_prop_kind(
    &self,
    idx_key: TypeId,
    kind: PropKeyKind,
    mode: RelationMode,
    depth: usize,
  ) -> bool {
    self.indexer_key_accepts_prop_kind_inner(idx_key, kind, mode, depth, 0)
  }

  fn indexer_key_accepts_prop_kind_inner(
    &self,
    idx_key: TypeId,
    kind: PropKeyKind,
    mode: RelationMode,
    depth: usize,
    match_depth: usize,
  ) -> bool {
    if match_depth >= self.limits.max_indexer_key_match_depth {
      return false;
    }

    match self.store.type_kind(idx_key) {
      TypeKind::String | TypeKind::StringLiteral(_) => {
        matches!(kind, PropKeyKind::String | PropKeyKind::Number)
      }
      TypeKind::Number | TypeKind::NumberLiteral(_) => matches!(kind, PropKeyKind::Number),
      TypeKind::Symbol | TypeKind::UniqueSymbol => matches!(kind, PropKeyKind::Symbol),
      TypeKind::Union(members) => members.iter().any(|member| {
        self.indexer_key_accepts_prop_kind_inner(*member, kind, mode, depth + 1, match_depth + 1)
      }),
      TypeKind::Intersection(members) => members.iter().all(|member| {
        self.indexer_key_accepts_prop_kind_inner(*member, kind, mode, depth + 1, match_depth + 1)
      }),
      _ => {
        let key_ty = match kind {
          PropKeyKind::String => self.store.primitive_ids().string,
          PropKeyKind::Number => self.store.primitive_ids().number,
          PropKeyKind::Symbol => self.store.primitive_ids().symbol,
        };
        self
          .relate_internal(
            key_ty,
            idx_key,
            RelationKind::Assignable,
            mode,
            false,
            depth,
          )
          .result
      }
    }
  }

  fn prop_key_kind(&self, key: &PropKey) -> PropKeyKind {
    match key {
      PropKey::String(_) => PropKeyKind::String,
      PropKey::Number(_) => PropKeyKind::Number,
      PropKey::Symbol(_) => PropKeyKind::Symbol,
    }
  }

  fn find_property<'b>(&self, shape: &'b Shape, key: &PropKey) -> Option<&'b Property> {
    let lookup = |key: &PropKey| {
      shape
        .properties
        .binary_search_by(|p| self.store.compare_prop_keys(&p.key, key))
        .ok()
        .map(|idx| &shape.properties[idx])
    };

    if let Some(hit) = lookup(key) {
      return Some(hit);
    }

    match key {
      PropKey::String(_) => parse_canonical_index_string(self.store.as_ref(), key)
        .and_then(|idx| lookup(&PropKey::Number(idx))),
      PropKey::Number(idx) if *idx >= 0 => {
        let name = self.store.intern_name(idx.to_string());
        lookup(&PropKey::String(name))
      }
      _ => None,
    }
  }

  fn expand_ref(&self, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    self
      .hooks
      .expander
      .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, args))
  }
}

fn parse_canonical_index_string(store: &TypeStore, key: &PropKey) -> Option<i64> {
  let PropKey::String(id) = key else {
    return None;
  };
  parse_canonical_index_str(&store.name(*id))
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

impl<'a> ConditionalAssignability for RelateCtx<'a> {
  fn is_assignable_for_conditional(&self, src: TypeId, dst: TypeId) -> bool {
    self.is_assignable_no_normalize(src, dst)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{Indexer, ObjectType, PropData, PropKey, Property, Shape, TypeKind, TypeStore};

  #[test]
  fn assignable_skip_normalize_does_not_invoke_normalize_type() {
    NORMALIZE_CALLS.with(|counter| counter.set(0));

    let store = TypeStore::new();
    let ctx = RelateCtx::new(store.clone(), store.options());
    let primitives = store.primitive_ids();

    // src: { [key: string | number]: number }
    let key_type = store.union(vec![primitives.string, primitives.number]);
    let mut src_shape = Shape::new();
    src_shape.indexers.push(Indexer {
      key_type,
      value_type: primitives.number,
      readonly: false,
    });
    let src_shape_id = store.intern_shape(src_shape);
    let src_obj = store.intern_object(ObjectType {
      shape: src_shape_id,
    });
    let src_ty = store.intern_type(TypeKind::Object(src_obj));

    // dst: { foo: number }
    let foo = store.intern_name("foo");
    let mut dst_shape = Shape::new();
    dst_shape.properties.push(Property {
      key: PropKey::String(foo),
      data: PropData {
        ty: primitives.number,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
    let dst_shape_id = store.intern_shape(dst_shape);
    let dst_obj = store.intern_object(ObjectType {
      shape: dst_shape_id,
    });
    let dst_ty = store.intern_type(TypeKind::Object(dst_obj));

    assert!(ctx.is_assignable_no_normalize(src_ty, dst_ty));
    assert_eq!(NORMALIZE_CALLS.with(|counter| counter.get()), 0);

    assert!(ctx.is_assignable(src_ty, dst_ty));
    assert!(NORMALIZE_CALLS.with(|counter| counter.get()) > 0);
  }

  #[test]
  fn relation_cache_separates_skip_normalize_mode() {
    let store = TypeStore::new();
    let ctx = RelateCtx::new(store.clone(), store.options());
    let primitives = store.primitive_ids();

    let key = store.intern_name("a");
    let base_obj = {
      let shape_id = store.intern_shape(Shape {
        properties: vec![Property {
          key: PropKey::String(key),
          data: PropData {
            ty: primitives.number,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        }],
        call_signatures: Vec::new(),
        construct_signatures: Vec::new(),
        indexers: Vec::new(),
      });
      let obj = store.intern_object(ObjectType { shape: shape_id });
      store.intern_type(TypeKind::Object(obj))
    };

    let key_a = store.intern_type(TypeKind::StringLiteral(key));
    let keyof_obj = store.intern_type(TypeKind::KeyOf(base_obj));

    // Skip-normalize mode cannot evaluate `keyof` and will treat the target as
    // an unsupported structural kind.
    assert!(
      !ctx
        .relate_internal(
          key_a,
          keyof_obj,
          RelationKind::Assignable,
          RelationMode::SKIP_NORMALIZE,
          false,
          1,
        )
        .result
    );

    // Normal mode normalizes `keyof` before the structural check and should not
    // be affected by the cached SKIP_NORMALIZE result.
    assert!(ctx.is_assignable(key_a, keyof_obj));
  }
}
