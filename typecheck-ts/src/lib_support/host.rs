use std::sync::Arc;

use crate::FileId;

use super::CompilerOptions;
use super::FileKind;
use super::LibFile;

/// Abstraction over file access and compiler configuration.
pub trait Host: Send + Sync {
  /// Entry files that should be checked.
  fn root_files(&self) -> Vec<FileId>;

  /// Text content for a file.
  fn file_text(&self, file: FileId) -> Arc<str>;

  /// File kind (ts/tsx/js/d.ts).
  fn file_kind(&self, file: FileId) -> FileKind;

  /// Resolve a module specifier from the given file into another `FileId`.
  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }

  /// Additional library files to include (e.g. ambient `.d.ts`).
  fn lib_files(&self) -> Vec<LibFile> {
    Vec::new()
  }

  /// Compiler options for this program.
  fn compiler_options(&self) -> CompilerOptions;
}
