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
      if code.starts_with("TC") || code.starts_with("BIND") {
        return false;
      }

      // `skipLibCheck` should suppress type/binder errors originating from
      // declaration files, but still surface diagnostics that affect module/lib
      // resolution. Keep a small allow-list of non-type-checking TS codes for
      // `.d.ts` files so failures like missing `/// <reference lib="..." />`
      // targets are still visible.
      if code.starts_with("TS") {
        return matches!(code, "TS6053" | "TS2688" | "TS2726");
      }

      true
    });
  }

  /// tsc `checkJs` semantics: a `.js` / `.jsx` file included via `allowJs`
  /// without `checkJs` is parsed (and can join the module graph) but produces
  /// **no semantic diagnostics** — not even TS2307 module-resolution errors
  /// (verified against tsc 5.9). Only parse/grammar diagnostics survive.
  fn filter_check_js_diagnostics(&self, diagnostics: &mut Vec<Diagnostic>) {
    if self.compiler_options.check_js == Some(true) {
      return;
    }

    diagnostics.retain(|diag| {
      let kind = self.file_kinds.get(&diag.primary.file);
      if !matches!(kind, Some(FileKind::Js) | Some(FileKind::Jsx)) {
        return true;
      }
      // Keep parse-level diagnostics only (mirrors the parse-error detection in
      // `db::queries::aggregate_program_diagnostics`). tsc also reports its
      // *grammar* diagnostics on private identifiers regardless of `checkJs`
      // (they are parser errors upstream): TS18016 (private name outside a
      // class), TS18028 (target too low), TS18030 (optional chain + private
      // identifier).
      let code = diag.code.as_str();
      code.starts_with("PS")
        || code == "TS1005"
        || code == "TS18016"
        || code == "TS18028"
        || code == "TS18030"
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
      self.filter_check_js_diagnostics(&mut diagnostics);
      return Ok(Arc::from(diagnostics));
    }
    self.check_cancelled()?;
    self.ensure_analyzed_result(host, roots)?;
    self.ensure_interned_types(host, roots)?;
    self.local_body_results.clear();
    self.set_extra_diagnostics_input();
    self.publish_body_context();

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

    // Warm the tracked body-check query for every body. Results are memoized
    // by salsa, so bodies untouched since the previous revision are cache hits
    // and everything downstream (`db::program_diagnostics`, `type_at`, span
    // queries) reuses the same memos.
    //
    // Parent body results (especially top-level bodies) seed bindings for many
    // child bodies, so check those sequentially first; salsa's cross-thread
    // memoization then shares them with all parallel workers (a worker hitting
    // an in-flight body blocks on the first computation instead of duplicating
    // it).
    let shared_context = self.body_check_context();
    let db = self.typecheck_db.clone();
    let mut results: Vec<(BodyId, Arc<BodyCheckResult>)> = Vec::new();
    let mut remaining: Vec<BodyId> = Vec::with_capacity(body_ids.len());
    for body in body_ids.iter().copied() {
      let is_top_level = shared_context
        .body_info
        .get(&body)
        .map(|info| matches!(info.kind, HirBodyKind::TopLevel))
        .unwrap_or(false);
      if is_top_level {
        results.push((body, db::check_body(&db, body)));
      } else {
        remaining.push(body);
      }
    }
    use rayon::prelude::*;
    // `map_with` clones the database handle per rayon split (salsa handles are
    // Send + Clone but not Sync); memoized state is shared through storage.
    let parallel_results: Vec<(BodyId, Arc<BodyCheckResult>)> = remaining
      .par_iter()
      .map_with(db.snapshot(), |db, body| (*body, db::check_body(db, *body)))
      .collect();
    results.extend(parallel_results);

    // Preserve determinism regardless of parallel scheduling.
    results.sort_by_key(|(id, _)| id.0);
    for (body, res) in results {
      self.local_body_results.insert(body, res);
    }

    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      let drained = {
        let mut sink = self
          .body_cache_stats_sink
          .lock()
          .unwrap_or_else(|err| err.into_inner());
        std::mem::take(&mut *sink)
      };
      self.cache_stats.merge(&drained);
    }

    let db = self.typecheck_db.clone();
    let mut diagnostics: Vec<_> = db::program_diagnostics(&db).as_ref().to_vec();
    diagnostics.extend(self.diagnostics.clone());
    // Dedupe rules: TS2352 by code+span (not message) — the same assertion may
    // be checked more than once via different paths with differently-displayed
    // but equivalent types, which would otherwise yield duplicates
    // (`typeAssertionsWithUnionTypes01`). All other codes dedupe by
    // code+span+message so legitimately distinct same-span diagnostics survive
    // (TS2318 emits one "Cannot find global type" per missing global at the
    // same file-level span — `triple_slash_no_default_lib`).
    let mut seen = HashSet::new();
    diagnostics.retain(|diag| {
      let key = if diag.code.as_str() == "TS2352" {
        (
          diag.code.clone(),
          diag.severity,
          diag.primary,
          String::new(),
        )
      } else {
        (
          diag.code.clone(),
          diag.severity,
          diag.primary,
          diag.message.clone(),
        )
      };
      seen.insert(key)
    });
    codes::normalize_diagnostics(&mut diagnostics);
    self.filter_skip_lib_check_diagnostics(&mut diagnostics);
    self.filter_check_js_diagnostics(&mut diagnostics);
    Ok(Arc::from(diagnostics))
  }
}
