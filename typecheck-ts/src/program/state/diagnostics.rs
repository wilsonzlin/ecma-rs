use super::*;

impl ProgramState {
  fn filter_skip_lib_check_diagnostics(&self, diagnostics: &mut Vec<Diagnostic>) {
    if !self.compiler_options.skip_lib_check {
      return;
    }

    diagnostics.retain(|diag| {
      if self.file_kinds.get(&diag.primary.file) != Some(&FileKind::Dts) {
        return true;
      }
      let code = diag.code.as_str();
      !code.starts_with("TC") && !code.starts_with("BIND")
    });
  }

  pub(super) fn program_diagnostics(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<Arc<[Diagnostic]>, FatalError> {
    if self.snapshot_loaded {
      let mut diagnostics = self.diagnostics.clone();
      self.filter_skip_lib_check_diagnostics(&mut diagnostics);
      return Ok(Arc::from(diagnostics));
    }
    self.check_cancelled()?;
    self.ensure_analyzed_result(host, roots)?;
    self.ensure_interned_types(host, roots)?;
    self.body_results.clear();
    self.set_extra_diagnostics_input();

    let body_ids: Vec<_> = {
      let db = self.typecheck_db.clone();
      let mut body_ids: Vec<_> = db::body_to_file(&db)
        .iter()
        .filter_map(|(body, file)| {
          let kind = db::file_kind(&db, *file);
          (!matches!(kind, FileKind::Dts)).then_some(*body)
        })
        .collect();
      body_ids.sort_by_key(|id| id.0);
      body_ids
    };

    let shared_context = self.body_check_context();
    // Parent body results (especially top-level bodies) are needed to seed bindings for many
    // child bodies. Compute these sequentially once and seed each parallel worker with the
    // results to avoid redundant work (and pathological contention) during parallel checking.
    let mut seed_results: Vec<(BodyId, Arc<BodyCheckResult>)> = Vec::new();
    let mut remaining: Vec<BodyId> = Vec::with_capacity(body_ids.len());
    let seed_db = BodyCheckDb::from_shared_context(Arc::clone(&shared_context));
    for body in body_ids.iter().copied() {
      let is_top_level = shared_context
        .body_info
        .get(&body)
        .map(|info| matches!(info.kind, HirBodyKind::TopLevel))
        .unwrap_or(false);
      if is_top_level {
        seed_results.push((body, db::queries::body_check::check_body(&seed_db, body)));
      } else {
        remaining.push(body);
      }
    }
    let seed_cache_stats = seed_db.into_cache_stats();
    let seed_results = Arc::new(seed_results);
    use rayon::prelude::*;
    let (cache_stats, mut results): (CheckerCacheStats, Vec<(BodyId, Arc<BodyCheckResult>)>) =
      remaining
        .par_iter()
        .fold(
          || {
            (
              BodyCheckDb::from_shared_context_with_seed_results(
                Arc::clone(&shared_context),
                seed_results.as_slice(),
              ),
              Vec::new(),
            )
          },
          |(db, mut results), body| {
            results.push((*body, db::queries::body_check::check_body(&db, *body)));
            (db, results)
          },
        )
        .map(|(db, results)| (db.into_cache_stats(), results))
        .reduce(
          || (CheckerCacheStats::default(), Vec::new()),
          |(mut stats, mut merged), (thread_stats, results)| {
            stats.merge(&thread_stats);
            merged.extend(results);
            (stats, merged)
          },
        );
    results.extend(seed_results.iter().map(|(id, res)| (*id, Arc::clone(res))));
    let mut cache_stats = cache_stats;
    cache_stats.merge(&seed_cache_stats);

    // Preserve determinism regardless of parallel scheduling.
    results.sort_by_key(|(id, _)| id.0);
    for (body, res) in results {
      self.body_results.insert(body, Arc::clone(&res));
      self.typecheck_db.set_body_result(body, res);
    }

    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      self.cache_stats.merge(&cache_stats);
    }

    let db = self.typecheck_db.clone();
    let mut diagnostics: Vec<_> = db::program_diagnostics(&db).as_ref().to_vec();
    diagnostics.extend(self.diagnostics.clone());
    let mut seen = HashSet::new();
    diagnostics.retain(|diag| {
      seen.insert((
        diag.code.clone(),
        diag.severity,
        diag.message.clone(),
        diag.primary,
      ))
    });
    codes::normalize_diagnostics(&mut diagnostics);
    self.filter_skip_lib_check_diagnostics(&mut diagnostics);
    Ok(Arc::from(diagnostics))
  }
}
