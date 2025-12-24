use crate::loc::Loc;
use crate::token::TT;
use core::fmt;
use core::fmt::Debug;
use core::fmt::Formatter;
#[cfg(feature = "diagnostics")]
use diagnostics::{Diagnostic, FileId, Span};
use std::error::Error;
use std::fmt::Display;

/// A stable classification of syntax errors produced by the parser.
///
/// Diagnostic codes (prefix `PS`) are assigned per variant and are stable:
/// - `PS0001`: [`SyntaxErrorType::ExpectedNotFound`]
/// - `PS0002`: [`SyntaxErrorType::ExpectedSyntax`]
/// - `PS0003`: [`SyntaxErrorType::InvalidAssigmentTarget`]
/// - `PS0004`: [`SyntaxErrorType::InvalidCharacterEscape`]
/// - `PS0005`: [`SyntaxErrorType::JsxClosingTagMismatch`]
/// - `PS0006`: [`SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters`]
/// - `PS0007`: [`SyntaxErrorType::LineTerminatorAfterThrow`]
/// - `PS0008`: [`SyntaxErrorType::LineTerminatorAfterYield`]
/// - `PS0009`: [`SyntaxErrorType::LineTerminatorInRegex`]
/// - `PS0010`: [`SyntaxErrorType::LineTerminatorInString`]
/// - `PS0011`: [`SyntaxErrorType::MalformedLiteralBigInt`]
/// - `PS0012`: [`SyntaxErrorType::MalformedLiteralNumber`]
/// - `PS0013`: [`SyntaxErrorType::RequiredTokenNotFound`]
/// - `PS0014`: [`SyntaxErrorType::TryStatementHasNoCatchOrFinally`]
/// - `PS0015`: [`SyntaxErrorType::UnexpectedEnd`]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SyntaxErrorType {
  ExpectedNotFound,
  ExpectedSyntax(&'static str),
  InvalidAssigmentTarget,
  InvalidCharacterEscape,
  JsxClosingTagMismatch,
  LineTerminatorAfterArrowFunctionParameters,
  LineTerminatorAfterThrow,
  LineTerminatorAfterYield,
  LineTerminatorInRegex,
  LineTerminatorInString,
  MalformedLiteralBigInt,
  MalformedLiteralNumber,
  RequiredTokenNotFound(TT),
  TryStatementHasNoCatchOrFinally,
  UnexpectedEnd,
}

#[derive(Clone)]
pub struct SyntaxError {
  pub typ: SyntaxErrorType,
  pub loc: Loc,
  pub actual_token: Option<TT>,
}

impl SyntaxError {
  pub fn new(typ: SyntaxErrorType, loc: Loc, actual_token: Option<TT>) -> SyntaxError {
    SyntaxError {
      typ,
      loc,
      actual_token,
    }
  }

  /// Convert this syntax error into a shared [`diagnostics::Diagnostic`].
  #[cfg(feature = "diagnostics")]
  pub fn to_diagnostic(&self, file: FileId) -> Diagnostic {
    let (range, overflow_note) = self.loc.to_diagnostics_range_with_note();
    let mut diagnostic = Diagnostic::error(
      self.typ.code(),
      self.typ.message(self.actual_token),
      Span::new(file, range),
    );

    if let Some(expected) = self.typ.expected_note() {
      diagnostic = diagnostic.with_note(expected);
    }
    if let Some(actual) = self.actual_token {
      diagnostic = diagnostic.with_note(format!("found token: {:?}", actual));
    }
    if let Some(note) = overflow_note {
      diagnostic = diagnostic.with_note(note);
    }

    diagnostic
  }
}

impl Debug for SyntaxError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{} around loc [{}:{}]", self, self.loc.0, self.loc.1)
  }
}

impl Display for SyntaxError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{:?} [token={:?}]", self.typ, self.actual_token)
  }
}

impl Error for SyntaxError {}

impl PartialEq for SyntaxError {
  fn eq(&self, other: &Self) -> bool {
    self.typ == other.typ
  }
}

impl Eq for SyntaxError {}

pub type SyntaxResult<T> = Result<T, SyntaxError>;

impl SyntaxErrorType {
  /// Stable diagnostic code for this syntax error variant.
  pub fn code(&self) -> &'static str {
    match self {
      SyntaxErrorType::ExpectedNotFound => "PS0001",
      SyntaxErrorType::ExpectedSyntax(_) => "PS0002",
      SyntaxErrorType::InvalidAssigmentTarget => "PS0003",
      SyntaxErrorType::InvalidCharacterEscape => "PS0004",
      SyntaxErrorType::JsxClosingTagMismatch => "PS0005",
      SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters => "PS0006",
      SyntaxErrorType::LineTerminatorAfterThrow => "PS0007",
      SyntaxErrorType::LineTerminatorAfterYield => "PS0008",
      SyntaxErrorType::LineTerminatorInRegex => "PS0009",
      SyntaxErrorType::LineTerminatorInString => "PS0010",
      SyntaxErrorType::MalformedLiteralBigInt => "PS0011",
      SyntaxErrorType::MalformedLiteralNumber => "PS0012",
      SyntaxErrorType::RequiredTokenNotFound(_) => "PS0013",
      SyntaxErrorType::TryStatementHasNoCatchOrFinally => "PS0014",
      SyntaxErrorType::UnexpectedEnd => "PS0015",
    }
  }

  /// Human-readable message describing this syntax error.
  pub fn message(&self, actual_token: Option<TT>) -> String {
    match self {
      SyntaxErrorType::ExpectedNotFound => "expected token not found".into(),
      SyntaxErrorType::ExpectedSyntax(expected) => format!("expected {}", expected),
      SyntaxErrorType::InvalidAssigmentTarget => "invalid assignment target".into(),
      SyntaxErrorType::InvalidCharacterEscape => "invalid character escape".into(),
      SyntaxErrorType::JsxClosingTagMismatch => "JSX closing tag does not match opening tag".into(),
      SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters => {
        "line terminator not allowed after arrow function parameters".into()
      }
      SyntaxErrorType::LineTerminatorAfterThrow => {
        "line terminator not allowed after `throw`".into()
      }
      SyntaxErrorType::LineTerminatorAfterYield => {
        "line terminator not allowed after `yield`".into()
      }
      SyntaxErrorType::LineTerminatorInRegex => {
        "line terminator not allowed in regular expression".into()
      }
      SyntaxErrorType::LineTerminatorInString => {
        "line terminator not allowed in string literal".into()
      }
      SyntaxErrorType::MalformedLiteralBigInt => "malformed bigint literal".into(),
      SyntaxErrorType::MalformedLiteralNumber => "malformed number literal".into(),
      SyntaxErrorType::RequiredTokenNotFound(token) => format!("expected token {:?}", token),
      SyntaxErrorType::TryStatementHasNoCatchOrFinally => {
        "try statement requires a catch or finally block".into()
      }
      SyntaxErrorType::UnexpectedEnd => actual_token
        .map(|tok| format!("unexpected end before {:?}", tok))
        .unwrap_or_else(|| "unexpected end of input".into()),
    }
  }

  #[cfg(feature = "diagnostics")]
  fn expected_note(&self) -> Option<String> {
    match self {
      SyntaxErrorType::ExpectedNotFound => Some("expected a token here".into()),
      SyntaxErrorType::ExpectedSyntax(expected) => Some(format!("expected {}", expected)),
      SyntaxErrorType::RequiredTokenNotFound(token) => Some(format!("expected token {:?}", token)),
      _ => None,
    }
  }
}
