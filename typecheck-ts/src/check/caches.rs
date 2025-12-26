use crate::check::instantiate::InstantiationCache;
use crate::lib_support::{CacheMode, CacheOptions};
use crate::profile::{CacheKind, QueryStatsCollector};
use types_ts_interned::{CacheStats, EvaluatorCaches, RelationCache};

/// Program-wide cache controller that can vend either shared or per-body caches
/// based on [`CacheOptions::mode`].
#[derive(Clone, Debug)]
pub struct CheckerCaches {
  options: CacheOptions,
  shared_relation: Option<RelationCache>,
  shared_eval: Option<EvaluatorCaches>,
  shared_instantiation: Option<InstantiationCache>,
}

impl CheckerCaches {
  /// Create caches according to the supplied options. When [`CacheMode::Shared`]
  /// is selected, the caches are retained and reused across [`BodyCaches`]
  /// instances; otherwise each call to [`CheckerCaches::for_body`] will create a
  /// fresh cache set.
  pub fn new(options: CacheOptions) -> Self {
    let shared = matches!(options.mode, CacheMode::Shared);
    let relation = shared.then(|| RelationCache::new(options.relation_config()));
    let eval = shared.then(|| EvaluatorCaches::new(options.eval_config()));
    let instantiation =
      shared.then(|| InstantiationCache::with_config(options.instantiation_config()));
    Self {
      options,
      shared_relation: relation,
      shared_eval: eval,
      shared_instantiation: instantiation,
    }
  }

  /// Obtain caches for checking a single body.
  pub fn for_body(&self) -> BodyCaches {
    match self.options.mode {
      CacheMode::Shared => BodyCaches {
        relation: self
          .shared_relation
          .clone()
          .unwrap_or_else(|| RelationCache::new(self.options.relation_config())),
        eval: self
          .shared_eval
          .clone()
          .unwrap_or_else(|| EvaluatorCaches::new(self.options.eval_config())),
        instantiation: self
          .shared_instantiation
          .clone()
          .unwrap_or_else(|| InstantiationCache::with_config(self.options.instantiation_config())),
      },
      CacheMode::PerBody => BodyCaches::new(
        self.options.relation_config(),
        self.options.eval_config(),
        self.options.instantiation_config(),
      ),
    }
  }

  /// Snapshot cache statistics for the shared caches (if any). Per-body caches
  /// should use [`BodyCaches::stats`].
  pub fn stats(&self) -> CheckerCacheStats {
    CheckerCacheStats::from_caches(
      self.shared_relation.as_ref(),
      self.shared_eval.as_ref(),
      self.shared_instantiation.as_ref(),
    )
  }
}

/// Per-body cache handles.
#[derive(Clone, Debug)]
pub struct BodyCaches {
  pub relation: RelationCache,
  pub eval: EvaluatorCaches,
  pub instantiation: InstantiationCache,
}

impl BodyCaches {
  fn new(
    relation_config: types_ts_interned::CacheConfig,
    eval_config: types_ts_interned::CacheConfig,
    instantiation_config: types_ts_interned::CacheConfig,
  ) -> Self {
    Self {
      relation: RelationCache::new(relation_config),
      eval: EvaluatorCaches::new(eval_config),
      instantiation: InstantiationCache::with_config(instantiation_config),
    }
  }

  /// Reset all caches to an empty state. Useful when reusing [`BodyCaches`] while
  /// running multiple bodies sequentially.
  pub fn clear(&self) {
    self.relation.clear();
    self.eval.clear();
    self.instantiation.clear();
  }

  /// Snapshot statistics for these caches.
  pub fn stats(&self) -> CheckerCacheStats {
    CheckerCacheStats::from_caches(
      Some(&self.relation),
      Some(&self.eval),
      Some(&self.instantiation),
    )
  }
}

/// Aggregated cache statistics aligned with [`CacheKind`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckerCacheStats {
  pub relation: CacheStats,
  pub eval: CacheStats,
  pub ref_expansion: CacheStats,
  pub instantiation: CacheStats,
}

impl CheckerCacheStats {
  fn from_caches(
    relation: Option<&RelationCache>,
    eval: Option<&EvaluatorCaches>,
    instantiation: Option<&InstantiationCache>,
  ) -> Self {
    let mut stats = CheckerCacheStats::default();
    if let Some(cache) = relation {
      stats.relation = cache.stats();
    }
    if let Some(caches) = eval {
      let eval_stats = caches.stats();
      stats.eval = eval_stats.eval;
      stats.ref_expansion = eval_stats.references;
    }
    if let Some(cache) = instantiation {
      stats.instantiation = cache.stats();
    }
    stats
  }

  /// Merge another stats snapshot into this one, summing all counters.
  pub fn merge(&mut self, other: &CheckerCacheStats) {
    self.relation.merge(&other.relation);
    self.eval.merge(&other.eval);
    self.ref_expansion.merge(&other.ref_expansion);
    self.instantiation.merge(&other.instantiation);
  }

  /// Compute the difference between two snapshots, saturating at zero to guard
  /// against counter resets.
  pub fn delta(&self, previous: &CheckerCacheStats) -> CheckerCacheStats {
    let sub = |a: CacheStats, b: CacheStats| CacheStats {
      hits: a.hits.saturating_sub(b.hits),
      misses: a.misses.saturating_sub(b.misses),
      insertions: a.insertions.saturating_sub(b.insertions),
      evictions: a.evictions.saturating_sub(b.evictions),
    };

    CheckerCacheStats {
      relation: sub(self.relation, previous.relation),
      eval: sub(self.eval, previous.eval),
      ref_expansion: sub(self.ref_expansion, previous.ref_expansion),
      instantiation: sub(self.instantiation, previous.instantiation),
    }
  }

  /// Record these stats into a query collector for profiling.
  pub fn record(&self, collector: &QueryStatsCollector) {
    collector.record_cache(CacheKind::Relation, &self.relation);
    collector.record_cache(CacheKind::Eval, &self.eval);
    collector.record_cache(CacheKind::RefExpansion, &self.ref_expansion);
    collector.record_cache(CacheKind::Instantiation, &self.instantiation);
  }
}
