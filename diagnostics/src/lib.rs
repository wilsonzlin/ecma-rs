#![doc = include_str!("../README.md")]
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

#[cfg(feature = "parse-js")]
use parse_js::error::SyntaxError;
#[cfg(feature = "parse-js")]
use parse_js::error::SyntaxErrorType;
#[cfg(feature = "parse-js")]
use parse_js::loc::Loc;
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

  /// Convert a `parse_js::loc::Loc` into a `TextRange`, saturating to `u32` if
  /// necessary and returning a note describing any truncation that occurred.
  #[cfg(feature = "parse-js")]
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

#[cfg(feature = "parse-js")]
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

/// Convert a parse-js [`SyntaxError`] into a [`Diagnostic`].
#[cfg(feature = "parse-js")]
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

#[cfg(feature = "parse-js")]
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

#[cfg(feature = "parse-js")]
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

  #[cfg(feature = "parse-js")]
  #[test]
  fn converts_syntax_error() {
    let err = SyntaxError::new(SyntaxErrorType::UnexpectedEnd, Loc(2, 5), None);
    let diagnostic = diagnostic_from_syntax_error(FileId(1), &err);
    assert_eq!(diagnostic.code, "PARSE0015");
    assert_eq!(diagnostic.primary.file, FileId(1));
    assert_eq!(diagnostic.primary.range, TextRange::new(2, 5));
    assert!(diagnostic.notes.is_empty());
  }

  #[cfg(feature = "parse-js")]
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
  fn contains_offset() {
    let span = Span::new(FileId(0), TextRange::new(2, 6));
    assert!(span.contains(2));
    assert!(span.contains(5));
    assert!(!span.contains(6));
  }

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
      "PARSE0015",
      "unexpected end of input",
      Span {
        file: FileId(1),
        range: TextRange::new(10, 10),
      },
    );

    let first = serde_json::to_string(&diagnostic).unwrap();
    let deserialized: Diagnostic = serde_json::from_str(&first).unwrap();
    let second = serde_json::to_string(&deserialized).unwrap();

    assert_eq!(deserialized.code, "PARSE0015");
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
