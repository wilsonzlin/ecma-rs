use super::*;

impl Program {
  /// Parse, bind, and type-check all known files, returning accumulated diagnostics.
  pub fn check(&self) -> Vec<Diagnostic> {
    match self.check_fallible() {
      Ok(diags) => diags,
      Err(fatal) => self.fatal_to_diagnostics(fatal),
    }
  }

  /// Fallible entry point that surfaces unrecoverable failures to the host.
  pub fn check_fallible(&self) -> Result<Vec<Diagnostic>, FatalError> {
    self
      .collect_program_diagnostics()
      .map(|diagnostics| diagnostics.to_vec())
  }

  fn collect_program_diagnostics(&self) -> Result<Arc<[Diagnostic]>, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.program_diagnostics(&self.host, &self.roots)
    })
  }

  /// Return collected query and cache statistics for this program.
  pub fn query_stats(&self) -> QueryStats {
    let (cache_stats, mut snapshot) = {
      let state = self.lock_state();
      let mut caches = state.cache_stats.clone();
      caches.merge(&state.checker_caches.stats());
      (caches, self.query_stats.snapshot())
    };

    let mut insert_cache = |kind: CacheKind, raw: &types_ts_interned::CacheStats| {
      let lookups = raw.hits + raw.misses;
      let stat = CacheStat {
        hits: raw.hits,
        misses: raw.misses,
        insertions: raw.insertions,
        evictions: raw.evictions,
        hit_rate: if lookups == 0 {
          0.0
        } else {
          raw.hits as f64 / lookups as f64
        },
      };
      snapshot.caches.insert(kind, stat);
    };

    insert_cache(CacheKind::Relation, &cache_stats.relation);
    insert_cache(CacheKind::Eval, &cache_stats.eval);
    insert_cache(CacheKind::RefExpansion, &cache_stats.ref_expansion);
    insert_cache(CacheKind::Instantiation, &cache_stats.instantiation);

    snapshot
  }
}
