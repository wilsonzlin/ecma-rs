use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;

use crate::lib_support::{CompilerOptions, FileKind, LibFile};
use crate::FileKey;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FileOrigin {
  Source,
  Lib,
}

#[derive(Clone, Debug)]
struct FileEntry {
  key: FileKey,
  origin: FileOrigin,
}

#[derive(Clone, Debug, Default)]
struct FileInterner {
  by_key: HashMap<(FileOrigin, FileKey), FileId>,
  entries: Vec<FileEntry>,
}

impl FileInterner {
  fn intern(&mut self, key: FileKey, origin: FileOrigin) -> (FileId, bool) {
    if let Some(existing) = self.by_key.get(&(origin, key.clone())) {
      return (*existing, false);
    }
    let id = FileId(self.entries.len() as u32);
    self.by_key.insert((origin, key.clone()), id);
    self.entries.push(FileEntry { key, origin });
    (id, true)
  }

  fn get(&self, key: &FileKey, origin: FileOrigin) -> Option<FileId> {
    self.by_key.get(&(origin, key.clone())).copied()
  }

  fn entry(&self, id: FileId) -> Option<&FileEntry> {
    self.entries.get(id.0 as usize)
  }

  fn len(&self) -> usize {
    self.entries.len()
  }
}

/// Host-provided inputs for the query database.
#[derive(Clone, Debug)]
pub struct Inputs {
  next_revision: u64,
  files_revision: u64,
  compiler_options: CompilerOptions,
  compiler_options_rev: u64,
  host_libs: Arc<[LibFile]>,
  host_libs_rev: u64,
  reachable_files: Arc<[FileId]>,
  reachable_files_rev: u64,
  interner: FileInterner,
  file_texts: HashMap<FileId, (Arc<str>, u64)>,
  file_kinds: HashMap<FileId, FileKind>,
}

impl Default for Inputs {
  fn default() -> Self {
    Inputs {
      next_revision: 1,
      files_revision: 0,
      compiler_options: CompilerOptions::default(),
      compiler_options_rev: 0,
      host_libs: Arc::from([]),
      host_libs_rev: 0,
      reachable_files: Arc::from([]),
      reachable_files_rev: 0,
      interner: FileInterner::default(),
      file_texts: HashMap::new(),
      file_kinds: HashMap::new(),
    }
  }
}

impl Inputs {
  pub fn new() -> Self {
    Inputs::default()
  }

  fn next_revision(&mut self) -> u64 {
    let rev = self.next_revision;
    self.next_revision = self.next_revision.saturating_add(1);
    rev
  }

  pub fn compiler_options(&self) -> &CompilerOptions {
    &self.compiler_options
  }

  pub fn set_compiler_options(&mut self, options: CompilerOptions) -> bool {
    if self.compiler_options == options {
      return false;
    }
    self.compiler_options = options;
    self.compiler_options_rev = self.next_revision();
    true
  }

  pub fn compiler_options_revision(&self) -> u64 {
    self.compiler_options_rev
  }

  pub fn set_host_libs(&mut self, libs: Vec<LibFile>) {
    self.host_libs = Arc::from(libs.into_boxed_slice());
    self.host_libs_rev = self.next_revision();
  }

  pub fn host_libs(&self) -> Arc<[LibFile]> {
    Arc::clone(&self.host_libs)
  }

  pub fn host_libs_revision(&self) -> u64 {
    self.host_libs_rev
  }

  pub fn set_reachable_files(&mut self, files: impl Into<Arc<[FileId]>>) {
    self.reachable_files = files.into();
    self.reachable_files_rev = self.next_revision();
  }

  pub fn reachable_files(&self) -> Arc<[FileId]> {
    Arc::clone(&self.reachable_files)
  }

  pub fn reachable_files_revision(&self) -> u64 {
    self.reachable_files_rev
  }

  pub fn files_revision(&self) -> u64 {
    self.files_revision
  }

  pub fn intern_file(&mut self, key: FileKey, origin: FileOrigin) -> FileId {
    let (id, inserted) = self.interner.intern(key, origin);
    if inserted {
      self.files_revision = self.next_revision();
    }
    id
  }

  pub fn file_id(&self, key: &FileKey, origin: FileOrigin) -> Option<FileId> {
    self.interner.get(key, origin)
  }

  pub fn file_key(&self, file: FileId) -> Option<&FileKey> {
    self.interner.entry(file).map(|entry| &entry.key)
  }

  pub fn file_origin(&self, file: FileId) -> Option<FileOrigin> {
    self.interner.entry(file).map(|entry| entry.origin)
  }

  pub fn file_count(&self) -> usize {
    self.interner.len()
  }

  pub fn set_file_text(&mut self, file: FileId, text: Arc<str>) {
    let revision = self.next_revision();
    self.file_texts.insert(file, (text, revision));
  }

  pub fn file_text(&self, file: FileId) -> Option<&Arc<str>> {
    self.file_texts.get(&file).map(|(text, _)| text)
  }

  pub fn file_text_revision(&self, file: FileId) -> u64 {
    self.file_texts.get(&file).map(|(_, rev)| *rev).unwrap_or(0)
  }

  pub fn set_file_kind(&mut self, file: FileId, kind: FileKind) {
    self.file_kinds.insert(file, kind);
  }

  pub fn file_kind(&self, file: FileId) -> Option<FileKind> {
    self.file_kinds.get(&file).copied()
  }
}
