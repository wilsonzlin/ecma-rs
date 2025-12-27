//! Incremental query database built on salsa.
//! This module is deliberately marked as `#[doc(hidden)]` at the crate root to
//! avoid promising a stable public API while we iterate on the query surface.
//! The types are `pub` so integration tests can exercise the database
//! end-to-end, but consumers should treat them as unstable internals.

use std::collections::BTreeMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use diagnostics::FileId;
use salsa::Setter;

use crate::lib_support::{CompilerOptions, FileKind};
use crate::FileKey;

mod inputs;
pub mod expander;
pub mod queries;

pub use inputs::CancellationToken;
pub use queries::{
  all_files, cancelled, compiler_options, db_revision, file_kind, file_text, global_bindings,
  lower_hir, module_resolve, parse, parse_query_count, reset_parse_query_count, roots, sem_hir,
  ts_semantics, GlobalBindingsDb, LowerResultWithDiagnostics, TsSemantics,
};

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
  fn module_resolution_input(&self, key: &ModuleKey) -> Option<inputs::ModuleResolutionInput>;
}

#[salsa::db]
#[derive(Clone)]
pub struct Database {
  storage: salsa::Storage<Self>,
  compiler_options_input: Option<inputs::CompilerOptionsInput>,
  roots_input: Option<inputs::RootsInput>,
  cancelled_input: Option<inputs::CancelledInput>,
  files: BTreeMap<FileId, inputs::FileInput>,
  file_keys: BTreeMap<FileKey, FileId>,
  module_resolutions: BTreeMap<ModuleKey, inputs::ModuleResolutionInput>,
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
      module_resolutions: BTreeMap::new(),
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
      .and_then(|id| self.files.get(id))
      .copied()
  }

  fn module_resolution_input(&self, key: &ModuleKey) -> Option<inputs::ModuleResolutionInput> {
    self.module_resolutions.get(key).copied()
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
  pub fn set_file(&mut self, file: FileId, key: FileKey, kind: FileKind, text: Arc<str>) {
    let key_id_entry = self.file_keys.entry(key.clone());
    match key_id_entry {
      std::collections::btree_map::Entry::Occupied(entry) => {
        assert_eq!(
          *entry.get(),
          file,
          "file key {:?} already registered to different id {:?}",
          key,
          entry.get()
        );
      }
      std::collections::btree_map::Entry::Vacant(entry) => {
        entry.insert(file);
      }
    }
    if let Some(existing) = self.files.get(&file).copied() {
      let old_key = existing.key(self);
      if old_key != key {
        self.file_keys.remove(&old_key);
        self.file_keys.insert(key.clone(), file);
      }
      existing.set_key(self).to(key);
      existing.set_kind(self).to(kind);
      existing.set_text(self).to(text);
    } else {
      let input = inputs::FileInput::new(self, file, key, kind, text);
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
    self.set_file(file, key, kind, text);
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
    self.set_file(file, key, kind, text);
  }

  /// Seed or update a module resolution edge.
  pub fn set_module_resolution(
    &mut self,
    from: FileId,
    specifier: Arc<str>,
    resolved: Option<FileId>,
  ) {
    let key = ModuleKey::new(from, specifier.clone());
    if let Some(existing) = self.module_resolutions.get(&key).copied() {
      existing.set_from_file(self).to(from);
      existing.set_specifier(self).to(specifier);
      existing.set_resolved(self).to(resolved);
    } else {
      let input = inputs::ModuleResolutionInput::new(self, from, specifier, resolved);
      self.module_resolutions.insert(key, input);
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

  pub fn all_files(&self) -> Arc<Vec<FileId>> {
    queries::all_files(self)
  }

  pub fn ts_semantics(&self) -> Arc<queries::TsSemantics> {
    queries::ts_semantics(self)
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
