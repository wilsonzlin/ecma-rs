#![doc = include_str!("../README.md")]
//! Shared diagnostics model and rendering utilities.
//!
//! The data structures here are intentionally minimal and deterministic so they
//! can be reused across parsing, binding, and type checking without pulling in
//! any heavy dependencies.
//!
//! ```
//! use diagnostics::files::SimpleFiles;
//! use diagnostics::render::render_diagnostic;
//! use diagnostics::{Diagnostic, Span, TextRange};
//!
//! let mut files = SimpleFiles::new();
//! let file = files.add("example.js", "let x = 1;");
//! let diag = Diagnostic::error(
//!   "TEST0001",
//!   "an example error",
//!   Span {
//!     file,
//!     range: TextRange::new(4, 5),
//!   },
//! );
//!
//! let rendered = render_diagnostic(&files, &diag);
//! assert!(rendered.contains("TEST0001"));
//! assert!(rendered.contains("--> example.js:1:5"));
//! ```

pub mod files;
pub mod render;
pub use files::SimpleFiles;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::fmt::Display;
use std::fmt::Formatter;

/// A stable identifier for a file in a program.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct FileId(pub u32);

/// A byte range in a file.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct TextRange {
  pub start: u32,
  pub end: u32,
}

impl TextRange {
  pub const fn new(start: u32, end: u32) -> Self {
    Self { start, end }
  }

  pub fn len(&self) -> u32 {
    self.end.saturating_sub(self.start)
  }

  /// Returns true if the given offset is within the range (inclusive start,
  /// exclusive end).
  pub fn contains(&self, offset: u32) -> bool {
    offset >= self.start && offset < self.end
  }

  pub fn is_empty(&self) -> bool {
    self.start >= self.end
  }
}

/// A span across a specific file.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Span {
  pub file: FileId,
  pub range: TextRange,
}

impl Span {
  pub const fn new(file: FileId, range: TextRange) -> Self {
    Self { file, range }
  }

  pub fn contains(&self, offset: u32) -> bool {
    self.range.contains(offset)
  }
}

/// Diagnostic severity.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Severity {
  Error,
  Warning,
  Note,
  Help,
}

impl Severity {
  pub const fn as_str(&self) -> &'static str {
    match self {
      Severity::Error => "error",
      Severity::Warning => "warning",
      Severity::Note => "note",
      Severity::Help => "help",
    }
  }
}

impl Display for Severity {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.write_str(self.as_str())
  }
}

/// A label attached to a diagnostic.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
  pub span: Span,
  pub message: String,
  pub is_primary: bool,
}

impl Label {
  pub fn new(span: Span, message: impl Into<String>, is_primary: bool) -> Self {
    Self {
      span,
      message: message.into(),
      is_primary,
    }
  }

  pub fn primary(span: Span, message: impl Into<String>) -> Self {
    Self::new(span, message, true)
  }

  pub fn secondary(span: Span, message: impl Into<String>) -> Self {
    Self::new(span, message, false)
  }
}

impl PartialOrd for Label {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Label {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    other
      .is_primary
      .cmp(&self.is_primary)
      .then_with(|| self.span.cmp(&other.span))
      .then_with(|| self.message.cmp(&other.message))
  }
}

/// A diagnostic code that prefers borrowed `'static` values but can own a string
/// when deserialized.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DiagnosticCode(pub Cow<'static, str>);

impl DiagnosticCode {
  pub fn as_str(&self) -> &str {
    &self.0
  }
}

impl Display for DiagnosticCode {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.write_str(self.as_str())
  }
}

impl From<&'static str> for DiagnosticCode {
  fn from(value: &'static str) -> Self {
    Self(Cow::Borrowed(value))
  }
}

impl From<String> for DiagnosticCode {
  fn from(value: String) -> Self {
    Self(Cow::Owned(value))
  }
}

impl From<Cow<'static, str>> for DiagnosticCode {
  fn from(value: Cow<'static, str>) -> Self {
    Self(value)
  }
}

impl PartialEq<&str> for DiagnosticCode {
  fn eq(&self, other: &&str) -> bool {
    self.as_str() == *other
  }
}

impl PartialEq<DiagnosticCode> for &str {
  fn eq(&self, other: &DiagnosticCode) -> bool {
    *self == other.as_str()
  }
}

/// A user-facing diagnostic with optional labels and notes.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
  pub code: DiagnosticCode,
  pub severity: Severity,
  pub message: String,
  pub primary: Span,
  pub labels: Vec<Label>,
  pub notes: Vec<String>,
}

impl Diagnostic {
  pub fn new(
    severity: Severity,
    code: impl Into<DiagnosticCode>,
    message: impl Into<String>,
    primary: Span,
  ) -> Self {
    Self {
      code: code.into(),
      severity,
      message: message.into(),
      primary,
      labels: Vec::new(),
      notes: Vec::new(),
    }
  }

  pub fn error(code: impl Into<DiagnosticCode>, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Error, code, message, primary)
  }

  pub fn warning(
    code: impl Into<DiagnosticCode>,
    message: impl Into<String>,
    primary: Span,
  ) -> Self {
    Self::new(Severity::Warning, code, message, primary)
  }

  pub fn note(code: impl Into<DiagnosticCode>, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Note, code, message, primary)
  }

  pub fn help(code: impl Into<DiagnosticCode>, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Help, code, message, primary)
  }

  pub fn with_label(mut self, label: Label) -> Self {
    self.push_label(label);
    self
  }

  pub fn add_label(mut self, label: Label) -> Self {
    self.push_label(label);
    self
  }

  pub fn push_label(&mut self, label: Label) {
    self.labels.push(label);
  }

  pub fn with_note(mut self, note: impl Into<String>) -> Self {
    self.push_note(note);
    self
  }

  pub fn push_note(&mut self, note: impl Into<String>) {
    self.notes.push(note.into());
  }

  pub fn merge_related<I>(mut self, labels: I) -> Self
  where
    I: IntoIterator<Item = Label>,
  {
    self.labels.extend(labels);
    self
  }

  /// Canonical deterministic ordering for diagnostics: severity, code, primary
  /// span, then message.
  pub fn sort_key(&self) -> (Severity, &DiagnosticCode, Span, &str) {
    (
      self.severity,
      &self.code,
      self.primary,
      self.message.as_str(),
    )
  }
}

impl PartialOrd for Diagnostic {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Diagnostic {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.sort_key().cmp(&other.sort_key())
  }
}

/// Helper for emitting an Internal Compiler Error diagnostic (`ICE0001`).
pub fn ice(primary: Span, message: impl Into<String>) -> Diagnostic {
  Diagnostic::error("ICE0001", message, primary).with_note(
    "internal compiler error: this is a bug in the tool; please file an issue with a reproduction",
  )
}

/// Helper for emitting a host/environment failure diagnostic (`HOST0001`).
///
/// Provide a span when the failure can be tied back to user input; otherwise a
/// zero-length placeholder span is used so renderers can still produce output.
pub fn host_error(primary: Option<Span>, message: impl Into<String>) -> Diagnostic {
  let mut diagnostic = Diagnostic::error(
    "HOST0001",
    message,
    primary.unwrap_or_else(|| Span::new(FileId(0), TextRange::new(0, 0))),
  );
  if primary.is_none() {
    diagnostic =
      diagnostic.with_note("no source span available for this host error; input may be missing");
  }
  diagnostic
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::render::render_diagnostic;
  use crate::render::render_diagnostic_with_options;
  use crate::render::RenderOptions;
  use crate::render::SourceProvider;

  #[derive(Default)]
  struct TestSource {
    name: String,
    text: String,
  }

  impl SourceProvider for TestSource {
    fn file_name(&self, _file: FileId) -> Option<&str> {
      Some(&self.name)
    }

    fn file_text(&self, _file: FileId) -> Option<&str> {
      Some(&self.text)
    }
  }

  struct MultiSource {
    names: Vec<String>,
    texts: Vec<String>,
  }

  impl SourceProvider for MultiSource {
    fn file_name(&self, file: FileId) -> Option<&str> {
      self.names.get(file.0 as usize).map(|name| name.as_str())
    }

    fn file_text(&self, file: FileId) -> Option<&str> {
      self.texts.get(file.0 as usize).map(|text| text.as_str())
    }
  }

  #[test]
  fn render_single_line_span() {
    let source = TestSource {
      name: "test.js".into(),
      text: "let x = 1;".into(),
    };
    let diagnostic = Diagnostic::error(
      "TEST0001",
      "unused variable",
      Span {
        file: FileId(0),
        range: TextRange::new(4, 5),
      },
    );

    let rendered = render_diagnostic(&source, &diagnostic);
    let expected = "error[TEST0001]: unused variable\n --> test.js:1:5\n  |\n1 | let x = 1;\n  |     ^ unused variable\n";
    assert_eq!(rendered, expected);
  }

  #[test]
  fn render_multi_line_span() {
    let source = TestSource {
      name: "main.ts".into(),
      text: "function test() {\n  return 1;\n}\n".into(),
    };
    let diagnostic = Diagnostic::error(
      "TEST0002",
      "broken function",
      Span {
        file: FileId(0),
        range: TextRange::new(0, source.text.len() as u32),
      },
    );

    let rendered = render_diagnostic(&source, &diagnostic);
    let expected = concat!(
      "error[TEST0002]: broken function\n",
      " --> main.ts:1:1\n",
      "  |\n",
      "1 | function test() {\n",
      "  | ^^^^^^^^^^^^^^^^^ broken function\n",
      "2 |   return 1;\n",
      "  | ^^^^^^^^^^^\n",
      "3 | }\n",
      "  | ^\n",
    );
    assert_eq!(rendered, expected);
  }

  #[test]
  fn stable_label_ordering() {
    let source = TestSource {
      name: "order.js".into(),
      text: "abcdef".into(),
    };
    let primary = Span {
      file: FileId(0),
      range: TextRange::new(2, 3),
    };
    let diagnostic = Diagnostic::warning("TEST0003", "ordering", primary)
      .with_label(Label::secondary(
        Span {
          file: FileId(0),
          range: TextRange::new(4, 5),
        },
        "second",
      ))
      .with_label(Label::secondary(
        Span {
          file: FileId(0),
          range: TextRange::new(0, 1),
        },
        "first",
      ));

    let rendered = render_diagnostic(&source, &diagnostic);
    let first_pos = rendered.find("first").unwrap();
    let second_pos = rendered.find("second").unwrap();
    assert!(first_pos < second_pos);
  }

  #[test]
  fn renders_additional_files() {
    let source = MultiSource {
      names: vec!["a.js".into(), "b.js".into()],
      texts: vec!["const a = 1;".into(), "const b = 2;".into()],
    };
    let diagnostic = Diagnostic::error(
      "TEST0004",
      "primary",
      Span {
        file: FileId(1),
        range: TextRange::new(6, 7),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: FileId(0),
        range: TextRange::new(6, 7),
      },
      "secondary",
    ));

    let rendered = render_diagnostic(&source, &diagnostic);
    assert!(rendered.contains(" --> b.js:1:7"));
    assert!(rendered.contains(" --> a.js:1:7"));
  }

  #[test]
  fn render_handles_missing_text() {
    struct MissingSource;

    impl SourceProvider for MissingSource {
      fn file_name(&self, _file: FileId) -> Option<&str> {
        None
      }

      fn file_text(&self, _file: FileId) -> Option<&str> {
        None
      }
    }

    let diagnostic = Diagnostic::error(
      "TEST0005",
      "cannot read source",
      Span {
        file: FileId(0),
        range: TextRange::new(10, 5),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: FileId(0),
        range: TextRange::new(0, 0),
      },
      "secondary detail",
    ));

    let rendered = render_diagnostic(&MissingSource, &diagnostic);
    assert!(rendered.contains("<unknown file>"));
    assert!(rendered.contains("source unavailable"));
    assert!(rendered.contains("secondary detail"));
  }

  #[test]
  fn render_clamps_out_of_bounds_ranges() {
    let source = TestSource {
      name: "clamp.js".into(),
      text: "abc".into(),
    };
    let diagnostic = Diagnostic::error(
      "TEST0009",
      "oob",
      Span {
        file: FileId(0),
        range: TextRange::new(10, 20),
      },
    );

    let rendered = render_diagnostic(&source, &diagnostic);
    assert!(rendered.contains("1 | abc"));
    assert!(rendered.contains("^ oob"));
  }

  #[test]
  fn render_clamps_non_char_boundaries() {
    let source = TestSource {
      name: "utf8.js".into(),
      text: "écho".into(),
    };
    let diagnostic = Diagnostic::error(
      "TEST0012",
      "inside utf8 char",
      Span {
        file: FileId(0),
        range: TextRange::new(1, 2),
      },
    );

    let rendered = render_diagnostic(&source, &diagnostic);
    assert!(rendered.contains("1 | écho"));
    assert!(rendered.contains("inside utf8 char"));
  }

  #[test]
  fn render_expands_tabs() {
    let source = TestSource {
      name: "tab.js".into(),
      text: "\tlet x = 1;".into(),
    };
    let diagnostic = Diagnostic::error(
      "TEST0013",
      "tab width",
      Span {
        file: FileId(0),
        range: TextRange::new(5, 6),
      },
    );

    let rendered = render_diagnostic(&source, &diagnostic);
    assert!(rendered.contains("1 |   let x = 1;"));
    assert!(rendered.contains("^ tab width"));
  }

  #[test]
  fn render_coalesces_labels_on_same_line() {
    let source = TestSource {
      name: "same-line.js".into(),
      text: "let value = 1;".into(),
    };
    let diagnostic = Diagnostic::error(
      "TEST0006",
      "two labels",
      Span {
        file: FileId(0),
        range: TextRange::new(4, 9),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: FileId(0),
        range: TextRange::new(8, 9),
      },
      "secondary",
    ));

    let rendered = render_diagnostic(&source, &diagnostic);
    assert_eq!(rendered.matches("let value = 1;").count(), 1);
    assert!(rendered.contains("two labels"));
    assert!(rendered.contains("secondary"));
  }

  #[test]
  fn render_elides_large_spans() {
    let source = TestSource {
      name: "long.js".into(),
      text: "a\nb\nc\nd\ne\nf\n".into(),
    };
    let options = RenderOptions {
      max_lines_per_label: 2,
      context_lines: 0,
      render_secondary_files: true,
    };
    let diagnostic = Diagnostic::error(
      "TEST0007",
      "long span",
      Span {
        file: FileId(0),
        range: TextRange::new(0, source.text.len() as u32),
      },
    );

    let rendered = render_diagnostic_with_options(&source, &diagnostic, options);
    assert!(rendered.contains("... (4 lines elided)"));
    assert!(rendered.contains("1 | a"));
    assert!(rendered.contains("6 | f"));
  }

  #[test]
  fn render_orders_multiple_files_stably() {
    let source = MultiSource {
      names: vec!["a.js".into(), "b.js".into()],
      texts: vec!["a = 1".into(), "b = 2".into()],
    };
    let diagnostic = Diagnostic::warning(
      "TEST0008",
      "ordering",
      Span {
        file: FileId(1),
        range: TextRange::new(0, 0),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: FileId(0),
        range: TextRange::new(0, 0),
      },
      "secondary file",
    ));

    let rendered = render_diagnostic(&source, &diagnostic);
    let primary_idx = rendered.find(" --> b.js").unwrap();
    let secondary_idx = rendered.find(" --> a.js").unwrap();
    assert!(primary_idx < secondary_idx);
  }

  #[test]
  fn render_includes_context_lines() {
    let source = TestSource {
      name: "ctx.js".into(),
      text: "first\nsecond\nthird\n".into(),
    };
    let options = RenderOptions {
      context_lines: 1,
      ..RenderOptions::default()
    };
    let diagnostic = Diagnostic::error(
      "TEST0010",
      "context",
      Span {
        file: FileId(0),
        range: TextRange::new(6, 12),
      },
    );

    let rendered = render_diagnostic_with_options(&source, &diagnostic, options);
    assert!(rendered.contains("1 | first"));
    assert!(rendered.contains("2 | second"));
    assert!(rendered.contains("3 | third"));
  }

  #[test]
  fn render_skips_secondary_files_when_requested() {
    let source = MultiSource {
      names: vec!["primary.js".into(), "secondary.js".into()],
      texts: vec!["p".into(), "s".into()],
    };
    let diagnostic = Diagnostic::error(
      "TEST0011",
      "primary file only",
      Span {
        file: FileId(0),
        range: TextRange::new(0, 1),
      },
    )
    .with_label(Label::secondary(
      Span {
        file: FileId(1),
        range: TextRange::new(0, 1),
      },
      "should be hidden",
    ));
    let options = RenderOptions {
      render_secondary_files: false,
      ..RenderOptions::default()
    };

    let rendered = render_diagnostic_with_options(&source, &diagnostic, options);
    assert!(rendered.contains("primary.js"));
    assert!(!rendered.contains("secondary.js"));
    assert!(!rendered.contains("should be hidden"));
  }

  #[test]
  fn contains_offset() {
    let span = Span::new(FileId(0), TextRange::new(2, 6));
    assert!(span.contains(2));
    assert!(span.contains(5));
    assert!(!span.contains(6));
  }
<<<<<<< HEAD

  #[test]
  fn ice_helper_sets_defaults() {
    let span = Span::new(FileId(1), TextRange::new(1, 2));
    let diagnostic = ice(span, "boom");
    assert_eq!(diagnostic.code, "ICE0001");
    assert_eq!(diagnostic.primary, span);
    assert_eq!(diagnostic.severity, Severity::Error);
    assert!(diagnostic
      .notes
      .iter()
      .any(|note| note.contains("internal compiler error")));
  }

  #[test]
  fn host_error_without_span_adds_placeholder_and_note() {
    let diagnostic = host_error(None, "disk full");
    assert_eq!(diagnostic.code, "HOST0001");
    assert_eq!(diagnostic.primary.file, FileId(0));
    assert_eq!(diagnostic.primary.range, TextRange::new(0, 0));
    assert!(diagnostic
      .notes
      .iter()
      .any(|note| note.contains("no source span available")));
  }

  #[cfg(feature = "parse-js")]
  #[test]
  fn loc_conversion_is_lossless_when_fitting() {
    let loc = Loc(10, 20);
    let range: TextRange = loc.into();
    assert_eq!(range, TextRange::new(10, 20));
  }

  #[test]
  fn diagnostic_sorting_is_deterministic() {
    let file = FileId(0);
    let mut diagnostics = vec![
      Diagnostic::error(
        "CODE1",
        "later span",
        Span {
          file,
          range: TextRange::new(5, 6),
        },
      ),
      Diagnostic::error(
        "CODE1",
        "message tie",
        Span {
          file,
          range: TextRange::new(5, 6),
        },
      ),
      Diagnostic::warning(
        "CODE1",
        "warning",
        Span {
          file,
          range: TextRange::new(0, 1),
        },
      ),
      Diagnostic::error(
        "CODE0",
        "alpha",
        Span {
          file,
          range: TextRange::new(4, 5),
        },
      ),
      Diagnostic::error(
        "CODE1",
        "earlier span",
        Span {
          file,
          range: TextRange::new(3, 4),
        },
      ),
    ];

    diagnostics.sort();

    let ordered: Vec<_> = diagnostics
      .into_iter()
      .map(|diag| {
        (
          diag.severity,
          diag.code,
          diag.primary.range.start,
          diag.message,
        )
      })
      .collect();
    assert_eq!(
      ordered,
      vec![
        (
          Severity::Error,
          DiagnosticCode::from("CODE0"),
          4,
          "alpha".to_string()
        ),
        (
          Severity::Error,
          DiagnosticCode::from("CODE1"),
          3,
          "earlier span".to_string()
        ),
        (
          Severity::Error,
          DiagnosticCode::from("CODE1"),
          5,
          "later span".to_string()
        ),
        (
          Severity::Error,
          DiagnosticCode::from("CODE1"),
          5,
          "message tie".to_string()
        ),
        (
          Severity::Warning,
          DiagnosticCode::from("CODE1"),
          0,
          "warning".to_string()
        ),
      ]
    );
  }

  #[cfg(feature = "serde")]
  #[test]
  fn serde_roundtrip_parse_error_code() {
    let diagnostic = Diagnostic::error(
      "PS0015",
      "unexpected end of input",
      Span {
        file: FileId(1),
        range: TextRange::new(10, 10),
      },
    );

    let first = serde_json::to_string(&diagnostic).unwrap();
    let deserialized: Diagnostic = serde_json::from_str(&first).unwrap();
    let second = serde_json::to_string(&deserialized).unwrap();

    assert_eq!(deserialized.code, "PS0015");
    assert_eq!(first, second);
  }

  #[cfg(feature = "serde")]
  #[test]
  fn serde_roundtrip_multi_label_with_notes() {
    let mut diagnostic = Diagnostic::warning(
      "TEST1234",
      "multi-label diagnostic",
      Span {
        file: FileId(0),
        range: TextRange::new(1, 2),
      },
    );
    diagnostic.push_label(Label::secondary(
      Span {
        file: FileId(0),
        range: TextRange::new(3, 4),
      },
      "secondary one",
    ));
    diagnostic.push_label(Label::secondary(
      Span {
        file: FileId(1),
        range: TextRange::new(5, 6),
      },
      "secondary two",
    ));
    diagnostic.push_note("first note");
    diagnostic.push_note("second note");

    let first = serde_json::to_string(&diagnostic).unwrap();
    let deserialized: Diagnostic = serde_json::from_str(&first).unwrap();
    let second = serde_json::to_string(&deserialized).unwrap();

    assert_eq!(first, second);
    assert_eq!(deserialized.labels, diagnostic.labels);
    assert_eq!(deserialized.notes, diagnostic.notes);
    assert_eq!(deserialized.primary, diagnostic.primary);
  }
}
