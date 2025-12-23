use serde::Deserialize;
use serde::Serialize;
use std::collections::HashMap;
use tracing::instrument;

/// Interned type identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(transparent)]
pub struct TypeId(pub u32);

/// A tiny subset of TypeScript-like types used to exercise caches and
/// tracing. This is deliberately minimal while we flesh out infrastructure.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypeKind {
  Any,
  Unknown,
  Never,
  Number,
  String,
  Boolean,
  /// A small conditional form to model laziness and cache-heavy evaluation.
  Conditional {
    check: Box<TypeKind>,
    extends: Box<TypeKind>,
    true_type: Box<TypeKind>,
    false_type: Box<TypeKind>,
  },
}

#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
pub struct CacheStats {
  pub hits: u64,
  pub misses: u64,
  pub hit_rate: f64,
}

impl CacheStats {
  pub fn from_counts(hits: u64, misses: u64) -> Self {
    let total = hits + misses;
    let hit_rate = if total == 0 {
      0.0
    } else {
      hits as f64 / total as f64
    };
    Self {
      hits,
      misses,
      hit_rate,
    }
  }
}

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct TypeStoreStats {
  pub interner: CacheStats,
  pub instantiation: CacheStats,
}

/// A trivial type store with an interner and instantiation cache so we can
/// surface hit/miss ratios in profiling output.
#[derive(Debug, Default)]
pub struct TypeStore {
  interner: HashMap<TypeKind, TypeId>,
  kinds: Vec<TypeKind>,
  interner_hits: u64,
  interner_misses: u64,
  instantiation_cache: HashMap<(TypeId, Vec<TypeId>), TypeId>,
  instantiation_hits: u64,
  instantiation_misses: u64,
}

impl TypeStore {
  pub fn new() -> Self {
    Self::default()
  }

  #[instrument(skip(self), fields(kind = ?kind))]
  pub fn intern(&mut self, kind: TypeKind) -> TypeId {
    if let Some(id) = self.interner.get(&kind).copied() {
      self.interner_hits += 1;
      tracing::trace!(target: "types_ts::interner", cache_hit = true, ?id);
      return id;
    }

    self.interner_misses += 1;
    let id = TypeId(self.kinds.len() as u32);
    self.kinds.push(kind.clone());
    self.interner.insert(kind, id);
    tracing::trace!(target: "types_ts::interner", cache_hit = false, ?id);
    id
  }

  pub fn get(&self, id: TypeId) -> Option<&TypeKind> {
    self.kinds.get(id.0 as usize)
  }

  /// Instantiate a type with the given arguments. The semantics here are
  /// intentionally lightweight; the important part is cache accounting.
  #[instrument(skip(self, args), fields(base = ?base, args_len = args.len()))]
  pub fn instantiate(&mut self, base: TypeId, args: &[TypeId]) -> TypeId {
    let key = (base, args.to_vec());
    if let Some(id) = self.instantiation_cache.get(&key).copied() {
      self.instantiation_hits += 1;
      tracing::trace!(target: "types_ts::instantiate", cache_hit = true, ?id);
      return id;
    }

    self.instantiation_misses += 1;
    let base_kind = self.get(base).cloned().unwrap_or(TypeKind::Unknown);
    // Synthesize a small conditional to mirror heavier instantiation paths.
    let new_kind = TypeKind::Conditional {
      check: Box::new(base_kind),
      extends: Box::new(TypeKind::Any),
      true_type: Box::new(TypeKind::Unknown),
      false_type: Box::new(TypeKind::Never),
    };
    let id = self.intern(new_kind);
    self.instantiation_cache.insert(key, id);
    tracing::trace!(target: "types_ts::instantiate", cache_hit = false, ?id);
    id
  }

  pub fn interner_stats(&self) -> CacheStats {
    CacheStats::from_counts(self.interner_hits, self.interner_misses)
  }

  pub fn instantiation_stats(&self) -> CacheStats {
    CacheStats::from_counts(self.instantiation_hits, self.instantiation_misses)
  }
}
