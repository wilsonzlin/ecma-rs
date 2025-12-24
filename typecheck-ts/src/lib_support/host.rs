use std::sync::Arc;

use crate::FileId;

use super::CompilerOptions;
use super::FileKind;
use super::LibFile;

/// Legacy abstraction over file access and compiler configuration.
///
/// This is only used by the deprecated string-scanning lib checker. It is **not**
/// the real type checker host API.
#[deprecated(
  note = "lib_support::LibCheckHost is a legacy helper for the lib checker; it is not the real type checker host API."
)]
pub trait LibCheckHost: Send + Sync {
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
