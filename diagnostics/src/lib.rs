//! Shared diagnostics model and rendering utilities.
//!
//! The data structures here are intentionally minimal and deterministic so they
//! can be reused across parsing, binding, and type checking without pulling in
//! any heavy dependencies.
//!
//! ```
//! use diagnostics::render::{render_diagnostic, SourceProvider};
//! use diagnostics::{Diagnostic, FileId, Span, TextRange};
//!
//! struct SingleFile {
//!   name: String,
//!   text: String,
//! }
//!
//! impl SourceProvider for SingleFile {
//!   fn file_name(&self, _file: FileId) -> &str {
//!     &self.name
//!   }
//!
//!   fn file_text(&self, _file: FileId) -> &str {
//!     &self.text
//!   }
//! }
//!
//! let file = FileId(0);
//! let provider = SingleFile {
//!   name: "example.js".into(),
//!   text: "let x = 1;".into(),
//! };
//! let diag = Diagnostic::error(
//!   "TEST0001",
//!   "an example error",
//!   Span {
//!     file,
//!     range: TextRange::new(4, 5),
//!   },
//! );
//!
//! let rendered = render_diagnostic(&provider, &diag);
//! assert!(rendered.contains("TEST0001"));
//! assert!(rendered.contains("--> example.js:1:5"));
//! ```

pub mod render;

use parse_js::error::SyntaxError;
use parse_js::error::SyntaxErrorType;
use parse_js::loc::Loc;
use std::fmt::Display;
use std::fmt::Formatter;

/// A stable identifier for a file in a program.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct FileId(pub u32);

/// A byte range in a file.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

  pub fn is_empty(&self) -> bool {
    self.start >= self.end
  }

  /// Convert a `parse_js::loc::Loc` into a `TextRange`, saturating to `u32` if
  /// necessary and returning a note describing any truncation that occurred.
  pub fn from_loc_with_overflow_note(loc: Loc) -> (Self, Option<String>) {
    let (start, start_overflow) = saturating_to_u32(loc.0);
    let (end, end_overflow) = saturating_to_u32(loc.1);
    let note = if start_overflow || end_overflow {
      Some(format!(
        "byte offsets truncated to fit u32 (start={}, end={})",
        loc.0, loc.1
      ))
    } else {
      None
    };

    (Self { start, end }, note)
  }
}

impl From<Loc> for TextRange {
  /// Converts a `Loc` by saturating to `u32`. Use
  /// [`TextRange::from_loc_with_overflow_note`] when you need to surface
  /// truncation to the user.
  fn from(value: Loc) -> Self {
    let (start, _) = saturating_to_u32(value.0);
    let (end, _) = saturating_to_u32(value.1);
    Self { start, end }
  }
}

/// A span across a specific file.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Span {
  pub file: FileId,
  pub range: TextRange,
}

/// Diagnostic severity.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

/// A user-facing diagnostic with optional labels and notes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
  pub code: &'static str,
  pub severity: Severity,
  pub message: String,
  pub primary: Span,
  pub labels: Vec<Label>,
  pub notes: Vec<String>,
}

impl Diagnostic {
  pub fn new(
    severity: Severity,
    code: &'static str,
    message: impl Into<String>,
    primary: Span,
  ) -> Self {
    Self {
      code,
      severity,
      message: message.into(),
      primary,
      labels: Vec::new(),
      notes: Vec::new(),
    }
  }

  pub fn error(code: &'static str, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Error, code, message, primary)
  }

  pub fn warning(code: &'static str, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Warning, code, message, primary)
  }

  pub fn note(code: &'static str, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Note, code, message, primary)
  }

  pub fn help(code: &'static str, message: impl Into<String>, primary: Span) -> Self {
    Self::new(Severity::Help, code, message, primary)
  }

  pub fn with_label(mut self, label: Label) -> Self {
    self.labels.push(label);
    self
  }

  pub fn with_note(mut self, note: impl Into<String>) -> Self {
    self.notes.push(note.into());
    self
  }

  pub fn merge_related<I>(mut self, labels: I) -> Self
  where
    I: IntoIterator<Item = Label>,
  {
    self.labels.extend(labels);
    self
  }
}

/// Convert a parse-js [`SyntaxError`] into a [`Diagnostic`].
pub fn diagnostic_from_syntax_error(file: FileId, err: &SyntaxError) -> Diagnostic {
  let (range, note) = TextRange::from_loc_with_overflow_note(err.loc);
  let span = Span { file, range };
  let (code, message) =
    syntax_error_metadata(&err.typ, err.actual_token.map(|tok| format!("{:?}", tok)));
  let mut diagnostic = Diagnostic::error(code, message, span);
  if let Some(note) = note {
    diagnostic = diagnostic.with_note(note);
  }
  diagnostic
}

fn syntax_error_metadata(
  typ: &SyntaxErrorType,
  actual_token: Option<String>,
) -> (&'static str, String) {
  match typ {
    SyntaxErrorType::ExpectedNotFound => ("PARSE0001", "expected token not found".into()),
    SyntaxErrorType::ExpectedSyntax(expected) => ("PARSE0002", format!("expected {}", expected)),
    SyntaxErrorType::InvalidAssigmentTarget => ("PARSE0003", "invalid assignment target".into()),
    SyntaxErrorType::InvalidCharacterEscape => ("PARSE0004", "invalid character escape".into()),
    SyntaxErrorType::JsxClosingTagMismatch => (
      "PARSE0005",
      "JSX closing tag does not match opening tag".into(),
    ),
    SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters => (
      "PARSE0006",
      "line terminator not allowed after arrow function parameters".into(),
    ),
    SyntaxErrorType::LineTerminatorAfterThrow => (
      "PARSE0007",
      "line terminator not allowed after `throw`".into(),
    ),
    SyntaxErrorType::LineTerminatorAfterYield => (
      "PARSE0008",
      "line terminator not allowed after `yield`".into(),
    ),
    SyntaxErrorType::LineTerminatorInRegex => (
      "PARSE0009",
      "line terminator not allowed in regular expression".into(),
    ),
    SyntaxErrorType::LineTerminatorInString => (
      "PARSE0010",
      "line terminator not allowed in string literal".into(),
    ),
    SyntaxErrorType::MalformedLiteralBigInt => ("PARSE0011", "malformed bigint literal".into()),
    SyntaxErrorType::MalformedLiteralNumber => ("PARSE0012", "malformed number literal".into()),
    SyntaxErrorType::RequiredTokenNotFound(token) => {
      ("PARSE0013", format!("expected token {:?}", token))
    }
    SyntaxErrorType::TryStatementHasNoCatchOrFinally => (
      "PARSE0014",
      "try statement requires a catch or finally block".into(),
    ),
    SyntaxErrorType::UnexpectedEnd => (
      "PARSE0015",
      actual_token
        .map(|tok| format!("unexpected end before {}", tok))
        .unwrap_or_else(|| "unexpected end of input".into()),
    ),
  }
}

fn saturating_to_u32(value: usize) -> (u32, bool) {
  if value > u32::MAX as usize {
    (u32::MAX, true)
  } else {
    (value as u32, false)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::render::render_diagnostic;
  use crate::render::SourceProvider;

  #[derive(Default)]
  struct TestSource {
    name: String,
    text: String,
  }

  impl SourceProvider for TestSource {
    fn file_name(&self, _file: FileId) -> &str {
      &self.name
    }

    fn file_text(&self, _file: FileId) -> &str {
      &self.text
    }
  }

  struct MultiSource {
    names: Vec<String>,
    texts: Vec<String>,
  }

  impl SourceProvider for MultiSource {
    fn file_name(&self, file: FileId) -> &str {
      &self.names[file.0 as usize]
    }

    fn file_text(&self, file: FileId) -> &str {
      &self.texts[file.0 as usize]
    }
  }

  #[test]
  fn converts_syntax_error() {
    let err = SyntaxError::new(SyntaxErrorType::UnexpectedEnd, Loc(2, 5), None);
    let diagnostic = diagnostic_from_syntax_error(FileId(1), &err);
    assert_eq!(diagnostic.code, "PARSE0015");
    assert_eq!(diagnostic.primary.file, FileId(1));
    assert_eq!(diagnostic.primary.range, TextRange::new(2, 5));
    assert!(diagnostic.notes.is_empty());
  }

  #[test]
  fn records_overflow_note_from_loc() {
    let loc = Loc(usize::MAX - 1, usize::MAX);
    let err = SyntaxError::new(SyntaxErrorType::ExpectedNotFound, loc, None);
    let diagnostic = diagnostic_from_syntax_error(FileId(0), &err);
    assert_eq!(diagnostic.primary.range.start, u32::MAX);
    assert_eq!(diagnostic.primary.range.end, u32::MAX);
    assert_eq!(diagnostic.notes.len(), 1);
    assert!(diagnostic.notes[0].contains("truncated"));
  }

  #[test]
  fn render_single_line_span() {
    let source = TestSource {
      name: "test.js".into(),
      text: "let x = 1;".into(),
    };
    let diagnostic = Diagnostic::error("TEST0001", "unused variable", Span {
      file: FileId(0),
      range: TextRange::new(4, 5),
    });

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
    let diagnostic = Diagnostic::error("TEST0002", "broken function", Span {
      file: FileId(0),
      range: TextRange::new(0, source.text.len() as u32),
    });

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
    let diagnostic = Diagnostic::error("TEST0004", "primary", Span {
      file: FileId(1),
      range: TextRange::new(6, 7),
    })
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
  fn loc_conversion_is_lossless_when_fitting() {
    let loc = Loc(10, 20);
    let range: TextRange = loc.into();
    assert_eq!(range, TextRange::new(10, 20));
  }
}
