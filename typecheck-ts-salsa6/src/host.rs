use std::sync::Arc;

/// Identifier for a file within a [`Program`](crate::Program).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(pub u32);

impl From<u32> for FileId {
  fn from(value: u32) -> Self {
    FileId(value)
  }
}

/// Classification of a source file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FileKind {
  /// JavaScript without JSX.
  Js,
  /// JavaScript with JSX.
  Jsx,
  /// TypeScript without JSX.
  Ts,
  /// TypeScript with JSX.
  Tsx,
  /// Declaration file.
  Dts,
}

/// Resolves module specifiers from a given origin file to a target [`FileId`].
pub trait Resolver: Send + Sync {
  /// Resolve `spec` imported from `from` into a [`FileId`].
  fn resolve(&self, from: FileId, spec: &str) -> Option<FileId>;
}

/// Provides source text and configuration to the checker.
pub trait Host: Resolver + Send + Sync + 'static {
  /// Returns the UTF-8 source text for `file`.
  fn file_text(&self, file: FileId) -> Arc<str>;

  /// Returns the [`FileKind`] for `file`.
  fn file_kind(&self, file: FileId) -> FileKind;

  /// Returns the compiler options in effect.
  fn options(&self) -> crate::CompilerOptions;
}
