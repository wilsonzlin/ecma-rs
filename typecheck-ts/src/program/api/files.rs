use super::*;

impl Program {
  /// Create a new program from a host and root file list.
  pub fn new(host: impl Host, roots: Vec<FileKey>) -> Program {
    Program::with_lib_manager(host, roots, Arc::new(LibManager::new()))
  }

  /// Create a new program with a provided lib manager (useful for observing invalidation in tests).
  pub fn with_lib_manager(
    host: impl Host,
    mut roots: Vec<FileKey>,
    lib_manager: Arc<LibManager>,
  ) -> Program {
    let host: Arc<dyn Host> = Arc::new(host);
    let query_stats = QueryStatsCollector::default();
    let cancelled = Arc::new(AtomicBool::new(false));
    roots.sort_unstable_by(|a, b| a.as_str().cmp(b.as_str()));
    roots.dedup_by(|a, b| a.as_str() == b.as_str());
    let program = Program {
      host: Arc::clone(&host),
      roots,
      cancelled: Arc::clone(&cancelled),
      state: std::sync::Mutex::new(ProgramState::new(
        Arc::clone(&host),
        lib_manager,
        query_stats.clone(),
        Arc::clone(&cancelled),
      )),
      query_stats,
    };
    {
      let mut state = program.lock_state();
      for key in program.roots.iter().cloned() {
        state.intern_file_key(key, FileOrigin::Source);
      }
    }
    program
  }

  /// Compiler options used by this program.
  pub fn compiler_options(&self) -> CompilerOptions {
    match self.with_analyzed_state(|state| Ok(state.compiler_options.clone())) {
      Ok(opts) => opts,
      Err(fatal) => {
        self.record_fatal(fatal);
        CompilerOptions::default()
      }
    }
  }

  /// Override the compiler options for subsequent queries.
  pub fn set_compiler_options(&mut self, options: CompilerOptions) {
    {
      let mut state = self.lock_state();
      state.typecheck_db.set_compiler_options(options.clone());
      state.compiler_options = options.clone();
      state.compiler_options_override = Some(options.clone());
      state.checker_caches = CheckerCaches::new(options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      state.interned_store = None;
    }
    self.reset_state();
  }

  /// Override the text for a specific file and invalidate cached results.
  pub fn set_file_text(&mut self, file: FileId, text: Arc<str>) {
    {
      let mut state = self.lock_state();
      let Some(key) = state.file_key_for_id(file) else {
        return;
      };
      state.file_overrides.insert(key.clone(), Arc::clone(&text));
      if db::Db::file_input(&state.typecheck_db, file).is_some() {
        state.typecheck_db.set_file_text(file, text);
      }
    }
    self.reset_state();
  }

  /// Resolve a file key to its internal [`FileId`], if loaded.
  pub fn file_id(&self, key: &FileKey) -> Option<FileId> {
    match self.with_analyzed_state(|state| Ok(state.file_id_for_key(key))) {
      Ok(id) => id,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// All [`FileId`]s associated with a [`FileKey`], preferring source-origin IDs first.
  pub fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    self
      .with_analyzed_state(|state| Ok(state.file_ids_for_key(key)))
      .unwrap_or_default()
  }

  /// Resolve a loaded [`FileId`] back to its [`FileKey`], if available.
  pub fn file_key(&self, file: FileId) -> Option<FileKey> {
    let state = self.lock_state();
    state.file_key_for_id(file)
  }

  /// Text contents for a loaded file, if available from the host.
  pub fn file_text(&self, file: FileId) -> Option<Arc<str>> {
    match self.with_analyzed_state(|state| Ok(state.load_text(file, &self.host).ok())) {
      Ok(text) => text,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Cached `hir-js` lowering for a loaded file, if available.
  ///
  /// This exposes the lowering computed during analysis so downstream tools can
  /// share HIR IDs (`BodyId`/`ExprId`) with the type checker without having to
  /// re-lower the same parsed AST.
  pub fn hir_lowered(&self, file: FileId) -> Option<Arc<hir_js::LowerResult>> {
    match self.with_analyzed_state(|state| Ok(state.hir_lowered.get(&file).cloned())) {
      Ok(lowered) => lowered,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// All known file IDs in this program.
  pub fn files(&self) -> Vec<FileId> {
    self
      .with_analyzed_state(|state| {
        let mut files: Vec<FileId> = state.files.keys().copied().collect();
        files.sort_by_key(|id| id.0);
        Ok(files)
      })
      .unwrap_or_default()
  }

  /// All files reachable from the configured roots.
  pub fn reachable_files(&self) -> Vec<FileId> {
    self
      .with_analyzed_state(|state| {
        let mut files: Vec<FileId> = if state.snapshot_loaded {
          use std::collections::{BTreeMap, VecDeque};

          let mut edges: BTreeMap<FileId, Vec<FileId>> = BTreeMap::new();
          for (from, _specifier, resolved) in state.typecheck_db.module_resolutions_snapshot() {
            let Some(resolved) = resolved else {
              continue;
            };
            edges.entry(from).or_default().push(resolved);
          }
          for deps in edges.values_mut() {
            deps.sort_by_key(|id| id.0);
            deps.dedup();
          }

          let mut queue: VecDeque<FileId> = state.root_ids.iter().copied().collect();
          let mut libs: Vec<FileId> = state.lib_file_ids.iter().copied().collect();
          libs.sort_by_key(|id| id.0);
          queue.extend(libs);

          let mut visited = BTreeMap::<FileId, ()>::new();
          while let Some(file) = queue.pop_front() {
            if visited.contains_key(&file) {
              continue;
            }
            visited.insert(file, ());
            if let Some(deps) = edges.get(&file) {
              for dep in deps {
                queue.push_back(*dep);
              }
            }
          }

          visited
            .keys()
            .copied()
            .filter(|file| !state.lib_file_ids.contains(file))
            .collect()
        } else {
          state
            .typecheck_db
            .reachable_files()
            .iter()
            .copied()
            .filter(|file| !state.lib_file_ids.contains(file))
            .collect()
        };
        files.sort_by_key(|id| id.0);
        Ok(files)
      })
      .unwrap_or_default()
  }
}
