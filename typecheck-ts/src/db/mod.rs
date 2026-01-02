//! Incremental query database built on salsa.
//! This module is deliberately marked as `#[doc(hidden)]` at the crate root to
//! avoid promising a stable public API while we iterate on the query surface.
//! The types are `pub` so integration tests can exercise the database
//! end-to-end, but consumers should treat them as unstable internals.

use std::collections::BTreeMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use crate::files::FileOrigin;
use crate::lib_support::{CompilerOptions, FileKind};
use crate::profile::QueryStatsCollector;
use crate::FileKey;
use crate::{BodyCheckResult, BodyId, DefId};
use diagnostics::{Diagnostic, FileId};
use salsa::Setter;

pub mod cache;
pub mod expander;
mod inputs;
pub mod queries;
pub(crate) mod spans;
pub mod symbols;

pub use inputs::CancellationToken;
pub use queries::body_check::{
  set_parallel_tracker, BodyCheckContext, BodyCheckDb, BodyInfo, ParallelTracker,
};
pub use queries::{
  aggregate_diagnostics, aggregate_program_diagnostics, all_files, body_file, body_parent,
  body_parents_in_file, body_to_file, cache_stats, cancelled, compiler_options, db_revision,
  def_file, def_to_file, expr_at, file_kind, file_span_index, file_text, global_bindings,
  local_symbol_info, lower_hir, module_dep_diagnostics, module_deps, module_resolve,
  module_specifiers, parse, parse_query_count, program_diagnostics, reachable_files,
  reset_parse_query_count, roots, sem_hir, span_of_def, span_of_expr, symbol_occurrences,
  ts_semantics, type_at, unresolved_module_diagnostics, var_initializer, DeclInfo, DeclKind,
  GlobalBindingsDb, Initializer, LowerResultWithDiagnostics, SharedTypeStore, TsSemantics,
  TypeDatabase, TypeSemantics, TypesDatabase, VarInit,
};
pub use spans::FileSpanIndex;

pub trait TypecheckDatabase: Db {}
impl TypecheckDatabase for Database {}
pub type TypecheckDb = Database;

/// Unique key for module resolution inputs.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleKey {
  pub(crate) from_file: FileId,
  pub(crate) specifier: Arc<str>,
}

impl ModuleKey {
  pub fn new(from: FileId, specifier: Arc<str>) -> Self {
    Self {
      from_file: from,
      specifier,
    }
  }
}

/// Database trait implemented by all salsa handles in this crate.
#[salsa::db]
pub trait Db: salsa::Database + Send + 'static {
  fn compiler_options_input(&self) -> inputs::CompilerOptionsInput;
  fn roots_input(&self) -> inputs::RootsInput;
  fn cancelled_input(&self) -> inputs::CancelledInput;
  fn file_input(&self, file: FileId) -> Option<inputs::FileInput>;
  fn file_input_by_key(&self, key: &FileKey) -> Option<inputs::FileInput>;
  fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId>;
  fn lib_files(&self) -> Vec<FileId>;
  fn file_origin(&self, file: FileId) -> Option<FileOrigin>;
  fn module_resolution_input(&self, key: &ModuleKey) -> Option<inputs::ModuleResolutionInput>;
  fn module_resolution_input_ref(
    &self,
    from: FileId,
    specifier: &str,
  ) -> Option<inputs::ModuleResolutionInput>;
  fn extra_diagnostics_input(&self) -> Option<inputs::ExtraDiagnosticsInput>;
  fn profiler(&self) -> Option<QueryStatsCollector>;
  fn body_result(&self, body: BodyId) -> Option<Arc<BodyCheckResult>>;
}

#[salsa::db]
#[derive(Clone)]
pub struct Database {
  storage: salsa::Storage<Self>,
  compiler_options_input: Option<inputs::CompilerOptionsInput>,
  roots_input: Option<inputs::RootsInput>,
  cancelled_input: Option<inputs::CancelledInput>,
  files: BTreeMap<FileId, inputs::FileInput>,
  file_keys: BTreeMap<FileKey, Vec<FileId>>,
  file_origins: BTreeMap<FileId, FileOrigin>,
  module_resolutions: BTreeMap<FileId, BTreeMap<Arc<str>, inputs::ModuleResolutionInput>>,
  extra_diagnostics: Option<inputs::ExtraDiagnosticsInput>,
  profiler: Option<QueryStatsCollector>,
  body_results: BTreeMap<BodyId, inputs::BodyResultInput>,
}

impl Default for Database {
  fn default() -> Self {
    let mut db = Database {
      storage: salsa::Storage::default(),
      compiler_options_input: None,
      roots_input: None,
      cancelled_input: None,
      files: BTreeMap::new(),
      file_keys: BTreeMap::new(),
      file_origins: BTreeMap::new(),
      module_resolutions: BTreeMap::new(),
      extra_diagnostics: None,
      profiler: None,
      body_results: BTreeMap::new(),
    };
    db.initialize_defaults();
    db
  }
}

#[salsa::db]
impl salsa::Database for Database {
  fn salsa_event(&self, _event: &dyn Fn() -> salsa::Event) {}
}

#[salsa::db]
impl Db for Database {
  fn compiler_options_input(&self) -> inputs::CompilerOptionsInput {
    self
      .compiler_options_input
      .expect("compiler options must be initialized")
  }

  fn roots_input(&self) -> inputs::RootsInput {
    self.roots_input.expect("roots must be initialized")
  }

  fn cancelled_input(&self) -> inputs::CancelledInput {
    self
      .cancelled_input
      .expect("cancellation token must be initialized")
  }

  fn file_input(&self, file: FileId) -> Option<inputs::FileInput> {
    self.files.get(&file).copied()
  }

  fn file_input_by_key(&self, key: &FileKey) -> Option<inputs::FileInput> {
    self
      .file_keys
      .get(key)
      .and_then(|ids| ids.first())
      .and_then(|id| self.files.get(id))
      .copied()
  }

  fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    let mut ids = self.file_keys.get(key).cloned().unwrap_or_default();
    sort_ids(&mut ids, &self.file_origins);
    ids
  }

  fn lib_files(&self) -> Vec<FileId> {
    self
      .file_origins
      .iter()
      .filter_map(|(id, origin)| matches!(origin, FileOrigin::Lib).then_some(*id))
      .collect()
  }

  fn file_origin(&self, file: FileId) -> Option<FileOrigin> {
    self.file_origins.get(&file).copied()
  }

  fn module_resolution_input(&self, key: &ModuleKey) -> Option<inputs::ModuleResolutionInput> {
    self
      .module_resolutions
      .get(&key.from_file)
      .and_then(|inner| inner.get(key.specifier.as_ref()))
      .copied()
  }

  fn module_resolution_input_ref(
    &self,
    from: FileId,
    specifier: &str,
  ) -> Option<inputs::ModuleResolutionInput> {
    self
      .module_resolutions
      .get(&from)
      .and_then(|inner| inner.get(specifier))
      .copied()
  }

  fn extra_diagnostics_input(&self) -> Option<inputs::ExtraDiagnosticsInput> {
    self.extra_diagnostics.as_ref().copied()
  }

  fn profiler(&self) -> Option<QueryStatsCollector> {
    self.profiler.clone()
  }

  fn body_result(&self, body: BodyId) -> Option<Arc<BodyCheckResult>> {
    self
      .body_results
      .get(&body)
      .map(|input| input.result(self).clone())
  }
}

impl Database {
  /// Create a new database with default inputs populated.
  pub fn new() -> Self {
    Database::default()
  }

  fn initialize_defaults(&mut self) {
    self.compiler_options_input = Some(inputs::CompilerOptionsInput::new(
      self,
      CompilerOptions::default(),
    ));
    self.roots_input = Some(inputs::RootsInput::new(self, Arc::<[FileKey]>::from([])));
    self.cancelled_input = Some(inputs::CancelledInput::new(
      self,
      inputs::CancellationToken::new(Arc::default()),
    ));
  }

  /// Clone the database handle for use on another thread.
  ///
  /// Salsa 0.18 tracks per-thread state in the handle itself, so clones are
  /// the way to create parallel snapshots instead of the (removed)
  /// `ParallelDatabase` trait.
  pub fn snapshot(&self) -> Self {
    self.clone()
  }

  /// Set compiler options, creating the input on first use.
  pub fn set_compiler_options(&mut self, options: CompilerOptions) {
    let handle = self.ensure_compiler_options();
    handle.set_options(self).to(options);
  }

  /// Set the set of root files.
  pub fn set_roots(&mut self, roots: Arc<[FileKey]>) {
    let handle = self.ensure_roots();
    handle.set_roots(self).to(roots);
  }

  /// Set the cancellation token to be used by queries.
  pub fn set_cancellation_flag(&mut self, flag: Arc<AtomicBool>) {
    let handle = self.ensure_cancelled();
    handle
      .set_token(self)
      .to(inputs::CancellationToken::new(flag));
  }

  /// Set file kind and text for a given `FileId`.
  pub fn set_file(
    &mut self,
    file: FileId,
    key: FileKey,
    kind: FileKind,
    text: Arc<str>,
    origin: FileOrigin,
  ) {
    self.file_origins.insert(file, origin);
    let entry = self.file_keys.entry(key.clone()).or_default();
    if !entry.contains(&file) {
      entry.push(file);
    }
    sort_ids(entry, &self.file_origins);
    if let Some(existing) = self.files.get(&file).copied() {
      let old_key = existing.key(self);
      if old_key != key {
        if let Some(ids) = self.file_keys.get_mut(&old_key) {
          ids.retain(|id| id != &file);
        }
      }
      existing.set_key(self).to(key);
      existing.set_kind(self).to(kind);
      existing.set_text(self).to(text);
    } else {
      let input = inputs::FileInput::new(self, file, key, kind, text, None);
      self.files.insert(file, input);
    }
  }

  pub fn set_file_kind(&mut self, file: FileId, kind: FileKind) {
    let text = self
      .files
      .get(&file)
      .map(|input| input.text(self))
      .unwrap_or_else(|| Arc::<str>::from(""));
    let key = self
      .files
      .get(&file)
      .map(|input| input.key(self))
      .unwrap_or_else(|| panic!("file {:?} must be seeded before setting kind", file));
    let origin = self
      .file_origins
      .get(&file)
      .copied()
      .unwrap_or(FileOrigin::Source);
    self.set_file(file, key, kind, text, origin);
  }

  pub fn set_file_text(&mut self, file: FileId, text: Arc<str>) {
    let kind = self
      .files
      .get(&file)
      .map(|input| input.kind(self))
      .unwrap_or(FileKind::Ts);
    let key = self
      .files
      .get(&file)
      .map(|input| input.key(self))
      .unwrap_or_else(|| panic!("file {:?} must be seeded before setting text", file));
    let origin = self
      .file_origins
      .get(&file)
      .copied()
      .unwrap_or(FileOrigin::Source);
    self.set_file(file, key, kind, text, origin);
  }

  /// Seed or update a module resolution edge.
  pub fn set_module_resolution(
    &mut self,
    from: FileId,
    specifier: Arc<str>,
    resolved: Option<FileId>,
  ) {
    if let Some(existing) = self
      .module_resolutions
      .get(&from)
      .and_then(|inner| inner.get(specifier.as_ref()))
      .copied()
    {
      existing.set_resolved(self).to(resolved);
    } else {
      let input = inputs::ModuleResolutionInput::new(self, from, Arc::clone(&specifier), resolved);
      self
        .module_resolutions
        .entry(from)
        .or_insert_with(BTreeMap::new)
        .insert(specifier, input);
    }
  }

  /// Seed or update a module resolution edge without allocating an `Arc<str>` key
  /// when the resolution already exists.
  pub fn set_module_resolution_ref(
    &mut self,
    from: FileId,
    specifier: &str,
    resolved: Option<FileId>,
  ) {
    if let Some(existing) = self
      .module_resolutions
      .get(&from)
      .and_then(|inner| inner.get(specifier))
      .copied()
    {
      existing.set_resolved(self).to(resolved);
    } else {
      let specifier: Arc<str> = Arc::from(specifier);
      let input = inputs::ModuleResolutionInput::new(self, from, Arc::clone(&specifier), resolved);
      self
        .module_resolutions
        .entry(from)
        .or_insert_with(BTreeMap::new)
        .insert(specifier, input);
    }
  }

  pub fn set_extra_diagnostics(&mut self, diagnostics: Arc<[Diagnostic]>) {
    if let Some(existing) = self.extra_diagnostics {
      existing.set_diagnostics(self).to(diagnostics);
    } else {
      self.extra_diagnostics = Some(inputs::ExtraDiagnosticsInput::new(self, diagnostics));
    }
  }

  pub fn parse(&self, file: FileId) -> crate::queries::parse::ParseResult {
    queries::parse(self, file)
  }

  pub fn lower_hir(&self, file: FileId) -> queries::LowerResultWithDiagnostics {
    queries::lower_hir(self, file)
  }

  pub fn sem_hir(&self, file: FileId) -> semantic_js::ts::HirFile {
    queries::sem_hir(self, file)
  }

  pub fn module_specifiers(&self, file: FileId) -> Arc<[Arc<str>]> {
    queries::module_specifiers(self, file)
  }

  pub fn module_deps(&self, file: FileId) -> Arc<[FileId]> {
    queries::module_deps(self, file)
  }

  pub fn module_dep_diagnostics(&self, file: FileId) -> Arc<[diagnostics::Diagnostic]> {
    queries::module_dep_diagnostics(self, file)
  }

  pub fn reachable_files(&self) -> Arc<Vec<FileId>> {
    queries::reachable_files(self)
  }

  pub fn all_files(&self) -> Arc<Vec<FileId>> {
    queries::all_files(self)
  }

  pub fn ts_semantics(&self) -> Arc<queries::TsSemantics> {
    queries::ts_semantics(self)
  }

  pub fn set_profiler(&mut self, profiler: QueryStatsCollector) {
    self.profiler = Some(profiler);
  }

  /// Cache a checked body result for reuse by span and type queries.
  pub fn set_body_result(&mut self, body: BodyId, result: Arc<BodyCheckResult>) {
    if let Some(existing) = self.body_results.get(&body).copied() {
      existing.set_body(self).to(body);
      existing.set_result(self).to(result);
    } else {
      let input = inputs::BodyResultInput::new(self, body, result);
      self.body_results.insert(body, input);
    }
  }

  pub fn def_to_file(&self) -> Arc<BTreeMap<DefId, FileId>> {
    queries::def_to_file(self)
  }

  pub fn body_to_file(&self) -> Arc<BTreeMap<BodyId, FileId>> {
    queries::body_to_file(self)
  }

  pub fn body_parents_in_file(&self, file: FileId) -> Arc<BTreeMap<BodyId, BodyId>> {
    queries::body_parents_in_file(self, file)
  }

  pub fn def_file(&self, def: DefId) -> Option<FileId> {
    queries::def_file(self, def)
  }

  pub fn body_file(&self, body: BodyId) -> Option<FileId> {
    queries::body_file(self, body)
  }

  pub fn body_parent(&self, body: BodyId) -> Option<BodyId> {
    queries::body_parent(self, body)
  }

  fn ensure_compiler_options(&mut self) -> inputs::CompilerOptionsInput {
    match self.compiler_options_input {
      Some(handle) => handle,
      None => {
        let handle = inputs::CompilerOptionsInput::new(self, CompilerOptions::default());
        self.compiler_options_input = Some(handle);
        handle
      }
    }
  }

  fn ensure_roots(&mut self) -> inputs::RootsInput {
    match self.roots_input {
      Some(handle) => handle,
      None => {
        let handle = inputs::RootsInput::new(self, Arc::<[FileKey]>::from([]));
        self.roots_input = Some(handle);
        handle
      }
    }
  }

  fn ensure_cancelled(&mut self) -> inputs::CancelledInput {
    match self.cancelled_input {
      Some(handle) => handle,
      None => {
        let handle =
          inputs::CancelledInput::new(self, inputs::CancellationToken::new(Arc::default()));
        self.cancelled_input = Some(handle);
        handle
      }
    }
  }
}

fn sort_ids(ids: &mut Vec<FileId>, origins: &BTreeMap<FileId, FileOrigin>) {
  ids.sort_by_key(|id| {
    let origin = origins.get(id).copied().unwrap_or(FileOrigin::Source);
    (origin, id.0)
  });
  ids.dedup();
}
