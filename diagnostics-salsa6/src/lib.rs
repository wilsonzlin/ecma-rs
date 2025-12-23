#![deny(missing_docs)]

//! Lightweight diagnostic model shared across crates.

use core::fmt;

/// A closed range within a file, represented as UTF-8 byte offsets.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TextRange {
  /// Starting offset (inclusive).
  pub start: u32,
  /// Ending offset (exclusive).
  pub end: u32,
}

impl TextRange {
  /// Creates a new [`TextRange`].
  pub fn new(start: u32, end: u32) -> Self {
    Self { start, end }
  }
}

/// A span within a file.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span<FileId> {
  /// The file the span is associated with.
  pub file: FileId,
  /// The range within the file.
  pub range: TextRange,
}

impl<FileId> Span<FileId> {
  /// Creates a new [`Span`].
  pub fn new(file: FileId, range: TextRange) -> Self {
    Self { file, range }
  }
}

/// Diagnostic severity.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
  /// An error that prevents successful compilation.
  Error,
  /// A warning that should be surfaced to the user but does not block compilation.
  Warning,
  /// Informational note.
  Note,
}

/// Stable identifier for diagnostics.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticCode(pub &'static str);

impl fmt::Display for DiagnosticCode {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.0)
  }
}

/// A diagnostic message with optional source information.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic<FileId> {
  /// Severity of the diagnostic.
  pub severity: Severity,
  /// Stable code for the diagnostic.
  pub code: DiagnosticCode,
  /// Human-readable message.
  pub message: String,
  /// Primary span associated with the diagnostic.
  pub primary: Option<Span<FileId>>,
  /// Additional notes.
  pub notes: Vec<String>,
}

impl<FileId> Diagnostic<FileId> {
  /// Creates a new diagnostic with severity [`Severity::Error`].
  pub fn error(code: impl Into<DiagnosticCode>, message: impl Into<String>) -> Self {
    Self {
      severity: Severity::Error,
      code: code.into(),
      message: message.into(),
      primary: None,
      notes: Vec::new(),
    }
  }

  /// Attaches a primary span to the diagnostic.
  pub fn with_primary(mut self, span: Span<FileId>) -> Self {
    self.primary = Some(span);
    self
  }

  /// Adds a note to the diagnostic.
  pub fn with_note(mut self, note: impl Into<String>) -> Self {
    self.notes.push(note.into());
    self
  }
}

impl From<&'static str> for DiagnosticCode {
  fn from(value: &'static str) -> Self {
    DiagnosticCode(value)
  }
}
