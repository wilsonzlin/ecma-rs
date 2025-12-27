use salsa::Revision;
use std::sync::Arc;

use crate::api::DefId;
use crate::TypeId;
use types_ts_interned::{
  CacheConfig, CacheStats, ShardedCache, TypeId as InternedTypeId, TypeParamId,
};

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

/// Cached entry for a definition's types, covering both the legacy [`TypeStore`]
/// representation and the interned form used by `types-ts-interned`.
#[derive(Clone, Default, Debug)]
pub(crate) struct DefCacheEntry {
  pub store: Option<TypeId>,
  pub interned: Option<InternedTypeId>,
  pub type_params: Option<Vec<TypeParamId>>,
}

impl DefCacheEntry {
  pub(crate) fn with_store(mut self, ty: TypeId) -> Self {
    self.store = Some(ty);
    self
  }

  pub(crate) fn with_interned(mut self, ty: InternedTypeId) -> Self {
    self.interned = Some(ty);
    self
  }

  pub(crate) fn with_params(mut self, params: Vec<TypeParamId>) -> Self {
    self.type_params = Some(params);
    self
  }
}

/// Deterministic sharded cache for definition types.
#[derive(Debug, Clone)]
pub struct DefCache {
  inner: Arc<ShardedCache<CacheKey<DefId>, DefCacheEntry>>,
}

impl DefCache {
  pub(crate) fn new(config: CacheConfig) -> Self {
    Self {
      inner: Arc::new(ShardedCache::new(config)),
    }
  }

  pub(crate) fn len(&self) -> usize {
    self.inner.len()
  }

  pub(crate) fn clear(&self) {
    self.inner.clear();
  }

  pub(crate) fn stats(&self) -> CacheStats {
    self.inner.stats()
  }

  pub(crate) fn get_entry(&self, def: DefId, revision: Revision) -> Option<DefCacheEntry> {
    self.inner.get(&CacheKey::new(revision, def))
  }

  pub(crate) fn get_store(&self, def: DefId, revision: Revision) -> Option<TypeId> {
    self
      .inner
      .get(&CacheKey::new(revision, def))
      .and_then(|entry| entry.store)
  }

  pub(crate) fn insert_entry(&self, def: DefId, revision: Revision, entry: DefCacheEntry) {
    self.inner.insert(CacheKey::new(revision, def), entry);
  }

  pub(crate) fn insert_store(&self, def: DefId, revision: Revision, ty: TypeId) {
    self.insert_entry(def, revision, DefCacheEntry::default().with_store(ty));
  }

  pub(crate) fn insert_interned(&self, def: DefId, revision: Revision, ty: InternedTypeId) {
    self.insert_entry(def, revision, DefCacheEntry::default().with_interned(ty));
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

  pub(crate) fn len(&self) -> usize {
    self.inner.len()
  }

  pub(crate) fn clear(&self) {
    self.inner.clear();
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
