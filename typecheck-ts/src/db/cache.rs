use salsa::Revision;
use std::sync::Arc;

use crate::api::DefId;
use crate::TypeId;
use types_ts_interned::{CacheConfig, CacheStats, ShardedCache};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct CacheKey<K> {
  revision: Revision,
  key: K,
}

impl<K> CacheKey<K> {
  fn new(revision: Revision, key: K) -> Self {
    Self { revision, key }
  }
}

/// Deterministic cache for definition types.
#[derive(Debug, Clone)]
pub struct DefCache {
  inner: Arc<ShardedCache<CacheKey<DefId>, TypeId>>,
}

impl DefCache {
  pub(crate) fn new(config: CacheConfig) -> Self {
    Self {
      inner: Arc::new(ShardedCache::new(config)),
    }
  }

  pub(crate) fn stats(&self) -> CacheStats {
    self.inner.stats()
  }

  pub(crate) fn get(&self, def: DefId, revision: Revision) -> Option<TypeId> {
    self.inner.get(&CacheKey::new(revision, def))
  }

  pub(crate) fn insert(&self, def: DefId, revision: Revision, ty: TypeId) {
    self.inner.insert(CacheKey::new(revision, def), ty);
  }
}

/// Deterministic cache for body checking results.
#[derive(Debug, Clone)]
pub struct BodyCache {
  inner: Arc<ShardedCache<CacheKey<DefId>, TypeId>>,
}

impl BodyCache {
  pub(crate) fn new(config: CacheConfig) -> Self {
    Self {
      inner: Arc::new(ShardedCache::new(config)),
    }
  }

  pub(crate) fn stats(&self) -> CacheStats {
    self.inner.stats()
  }

  pub(crate) fn get(&self, def: DefId, revision: Revision) -> Option<TypeId> {
    self.inner.get(&CacheKey::new(revision, def))
  }

  pub(crate) fn insert(&self, def: DefId, revision: Revision, ty: TypeId) {
    self.inner.insert(CacheKey::new(revision, def), ty);
  }
}
