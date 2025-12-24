use crate::render::SourceProvider;
use crate::FileId;
use std::sync::Arc;

/// A minimal in-memory store of file names and source text for rendering
/// diagnostics in tests, CLIs, and harnesses without needing a custom
/// [`SourceProvider`] implementation.
///
/// `FileId`s are allocated deterministically in insertion order starting from
/// zero. Source text is stored in `Arc<str>` to make cloning cheap.
#[derive(Clone, Debug, Default)]
pub struct SimpleFiles {
  files: Vec<SimpleFile>,
}

#[derive(Clone, Debug)]
struct SimpleFile {
  name: Arc<str>,
  text: Arc<str>,
}

impl SimpleFiles {
  pub fn new() -> Self {
    Self::default()
  }

  /// Adds a new file and returns its [`FileId`]. The id is monotonically
  /// increasing and stable for the lifetime of the `SimpleFiles` instance.
  pub fn add(&mut self, name: impl Into<Arc<str>>, text: impl Into<Arc<str>>) -> FileId {
    assert!(self.files.len() < u32::MAX as usize, "file count overflow");
    let file = FileId(self.files.len() as u32);
    self.files.push(SimpleFile {
      name: name.into(),
      text: text.into(),
    });
    file
  }

  /// Replaces the text for an existing file, returning the previous text if the
  /// file existed.
  pub fn set_text(&mut self, file: FileId, text: impl Into<Arc<str>>) -> Option<Arc<str>> {
    self
      .files
      .get_mut(file.0 as usize)
      .map(|file| std::mem::replace(&mut file.text, text.into()))
  }

  /// Alias for [`set_text`] to align with some incremental APIs.
  pub fn replace_text(&mut self, file: FileId, text: impl Into<Arc<str>>) -> Option<Arc<str>> {
    self.set_text(file, text)
  }
}

impl SourceProvider for SimpleFiles {
  fn file_name(&self, file: FileId) -> Option<&str> {
    self.files.get(file.0 as usize).map(|file| file.name.as_ref())
  }

  fn file_text(&self, file: FileId) -> Option<&str> {
    self.files.get(file.0 as usize).map(|file| file.text.as_ref())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::render::render_diagnostic;
  use crate::{Diagnostic, Label, Span, TextRange};

  #[test]
  fn allocates_ids_and_renders_multiple_files() {
    let mut files = SimpleFiles::new();
    let first = files.add("a.js", "const a = 1;");
    let second = files.add("b.js", "const b = 2;");
    assert_ne!(first, second);

    let diagnostic = Diagnostic::error(
      "TEST0004",
      "primary",
      Span {
        file: second,
        range: TextRange::new(6, 7),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: first,
        range: TextRange::new(6, 7),
      },
      "secondary",
    ));

    let rendered = render_diagnostic(&files, &diagnostic);
    assert!(rendered.contains(" --> b.js:1:7"));
    assert!(rendered.contains(" --> a.js:1:7"));
  }

  #[test]
  fn missing_files_degrade_gracefully() {
    let mut files = SimpleFiles::new();
    let existing = files.add("a.js", "const a = 1;");
    let missing = FileId(existing.0 + 1);

    let diagnostic = Diagnostic::error(
      "TEST0005",
      "missing file",
      Span {
        file: missing,
        range: TextRange::new(0, 1),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: existing,
        range: TextRange::new(6, 7),
      },
      "secondary",
    ));

    assert!(files.file_name(missing).is_none());
    assert!(files.file_text(missing).is_none());

    let rendered = render_diagnostic(&files, &diagnostic);
    assert!(rendered.contains("<unknown>"));
    assert!(rendered.contains("<source unavailable>"));
  }
}
