//! Lightweight TypeScript-inspired type primitives and relation helpers.
//! This crate is intentionally minimal for now; it models a handful of
//! primitive types, a tiny interner, and relation/conditional evaluation
//! with cache statistics that can be surfaced by downstream tooling.

mod relate;
mod store;

pub use relate::RelateContext;
pub use relate::RelationCache;
pub use relate::RelationCacheStats;
pub use relate::RelationKind;
pub use store::CacheStats;
pub use store::TypeId;
pub use store::TypeKind;
pub use store::TypeStore;
pub use store::TypeStoreStats;

/// A bundle of cache statistics that callers can surface in profile output.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Default)]
pub struct CacheReport {
  pub relations: RelationCacheStats,
  pub interner: CacheStats,
  pub instantiation: CacheStats,
}

impl CacheReport {
  pub fn new(store: &TypeStore, relations: &RelationCache) -> Self {
    Self {
      relations: relations.stats(),
      interner: store.interner_stats(),
      instantiation: store.instantiation_stats(),
    }
  }
}
