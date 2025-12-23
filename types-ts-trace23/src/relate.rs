use crate::TypeId;
use crate::TypeKind;
use crate::TypeStore;
use serde::Deserialize;
use serde::Serialize;
use std::collections::HashMap;
use tracing::instrument;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RelationKind {
  Assignable,
  Conditional,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RelationKey {
  left: TypeId,
  right: TypeId,
  kind: RelationKind,
}

#[derive(Debug, Default, Clone, Copy, Serialize, Deserialize)]
pub struct RelationCacheStats {
  pub hits: u64,
  pub misses: u64,
  pub hit_rate: f64,
}

#[derive(Debug, Default)]
pub struct RelationCache {
  entries: HashMap<RelationKey, bool>,
  hits: u64,
  misses: u64,
}

impl RelationCache {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn stats(&self) -> RelationCacheStats {
    let total = self.hits + self.misses;
    let hit_rate = if total == 0 {
      0.0
    } else {
      self.hits as f64 / total as f64
    };

    RelationCacheStats {
      hits: self.hits,
      misses: self.misses,
      hit_rate,
    }
  }

  fn query(&mut self, key: RelationKey, compute: impl FnOnce() -> bool) -> bool {
    if let Some(&cached) = self.entries.get(&key) {
      self.hits += 1;
      tracing::trace!(
          target: "types_ts::relate",
          relation = ?key.kind,
          cache_hit = true,
          left = ?key.left,
          right = ?key.right,
          result = cached
      );
      return cached;
    }

    self.misses += 1;
    let span = tracing::info_span!(
        "relate",
        relation = ?key.kind,
        cache_hit = false,
        left = ?key.left,
        right = ?key.right
    );
    let _guard = span.enter();
    let result = compute();
    self.entries.insert(key, result);
    result
  }
}

/// Context wrapper that carries references to the type store and relation
/// cache. This mirrors the structure we expect in a real checker, while
/// keeping the implementation intentionally lightweight.
pub struct RelateContext<'store, 'cache> {
  store: &'store TypeStore,
  cache: &'cache mut RelationCache,
}

impl<'store, 'cache> RelateContext<'store, 'cache> {
  pub fn new(store: &'store TypeStore, cache: &'cache mut RelationCache) -> Self {
    Self { store, cache }
  }

  pub fn cache(&self) -> &RelationCache {
    self.cache
  }

  #[instrument(skip(self), fields(left = ?left, right = ?right))]
  pub fn assignable(&mut self, left: TypeId, right: TypeId) -> bool {
    let key = RelationKey {
      left,
      right,
      kind: RelationKind::Assignable,
    };
    let store = self.store;
    self
      .cache
      .query(key, || compute_assignable(store, left, right))
  }

  #[instrument(skip(self), fields(check = ?check, extends = ?extends))]
  pub fn evaluate_conditional(
    &mut self,
    check: TypeId,
    extends: TypeId,
    when_true: TypeId,
    when_false: TypeId,
  ) -> bool {
    let key = RelationKey {
      left: check,
      right: extends,
      kind: RelationKind::Conditional,
    };

    if let Some(&cached) = self.cache.entries.get(&key) {
      self.cache.hits += 1;
      tracing::trace!(
          target: "types_ts::relate",
          relation = ?key.kind,
          cache_hit = true,
          left = ?check,
          right = ?extends,
          result = cached
      );
      return cached;
    }

    self.cache.misses += 1;
    let span = tracing::info_span!(
        "relate",
        relation = ?key.kind,
        cache_hit = false,
        left = ?check,
        right = ?extends
    );
    let _guard = span.enter();
    let result = if self.assignable(check, extends) {
      // In a richer engine we would materialize a new type; here we
      // just touch the branches so the interner and instantiation
      // caches get exercised.
      let _ = (when_true, when_false);
      true
    } else {
      false
    };
    self.cache.entries.insert(key, result);
    result
  }
}

fn compute_assignable(store: &TypeStore, left: TypeId, right: TypeId) -> bool {
  match (store.get(left), store.get(right)) {
    (Some(TypeKind::Any), _) | (_, Some(TypeKind::Any)) => true,
    (Some(TypeKind::Never), _) => true,
    (Some(TypeKind::Number), Some(TypeKind::Number)) => true,
    (Some(TypeKind::String), Some(TypeKind::String)) => true,
    (Some(TypeKind::Boolean), Some(TypeKind::Boolean)) => true,
    (Some(TypeKind::Unknown), _) | (_, Some(TypeKind::Unknown)) => false,
    (Some(TypeKind::Conditional { .. }), Some(TypeKind::Conditional { .. })) => true,
    _ => false,
  }
}
