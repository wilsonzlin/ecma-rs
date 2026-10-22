use crate::loc::Loc;
use crate::token::TT;
use core::fmt;
use core::fmt::Debug;
use core::fmt::Formatter;
#[cfg(feature = "diagnostics")]
use diagnostics::{Diagnostic, FileId, ParseJsError, Span};
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
/// - `PS0016`: [`SyntaxErrorType::Cancelled`]
/// - `PS0017`: [`SyntaxErrorType::InvalidOptionalChainFromNew`]
/// - `PS0018`: [`SyntaxErrorType::DeclarationInSingleStatementPosition`]
/// - `PS0019`: [`SyntaxErrorType::BindingPatternRequiresInitializer`]
/// - `PS0020`: [`SyntaxErrorType::UnterminatedMultilineComment`]
/// - `PS0021`: [`SyntaxErrorType::InvalidRestParameter`]
/// - `PS0022`: [`SyntaxErrorType::NumericLiteralFollowedByIdentifier`]
/// - `PS0023`: [`SyntaxErrorType::HtmlCommentInModule`]
/// - `PS0024`: [`SyntaxErrorType::InvalidClassHeritage`]
/// - `PS0025`: [`SyntaxErrorType::LegacyOctalEscapeInTemplate`]
/// - `PS0026`: [`SyntaxErrorType::InvalidUpdateOperand`]
/// - `PS0027`: [`SyntaxErrorType::MixedNullishLogicalOperators`]
/// - `PS0028`: [`SyntaxErrorType::OptionalChainTaggedTemplate`]
/// - `PS0029`: [`SyntaxErrorType::InvalidPrivateIdentifier`]
/// - `PS0030`: [`SyntaxErrorType::InvalidCharacter`] (tsc TS1127)
/// - `PS0031`: [`SyntaxErrorType::VariableDeclarationExpected`] (tsc TS1134)
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
  Cancelled,
  /// Optional chain in/after a bare `new` expression (ECMA-262; mirrors TS1209).
  InvalidOptionalChainFromNew,
  /// Declaration where only Statement is allowed (ECMA-262 §14 Statement vs StatementListItem).
  DeclarationInSingleStatementPosition,
  /// `var`/`let`/`const` BindingPattern without Initializer (ECMA-262 §14.3.1/§14.3.2).
  BindingPatternRequiresInitializer,
  /// Unterminated MultiLineComment (ECMA-262 §12.4).
  UnterminatedMultilineComment,
  /// Rest parameter not last / with initializer / with trailing comma (ECMA-262 §15.1).
  InvalidRestParameter,
  /// NumericLiteral immediately followed by IdentifierStart (ECMA-262 §12.9.3).
  NumericLiteralFollowedByIdentifier,
  /// HTML-like comment in module code (ECMA-262 §B.1.1; script-only).
  HtmlCommentInModule,
  /// ClassHeritage is not a LeftHandSideExpression (ECMA-262 §15.7).
  InvalidClassHeritage,
  /// Legacy octal / non-octal decimal escape in a template literal (ECMA-262 §12.9.6).
  LegacyOctalEscapeInTemplate,
  /// UpdateExpression operand is not a simple assignment target (ECMA-262 §13.4).
  InvalidUpdateOperand,
  /// `??` mixed with `&&`/`||` without parentheses (ECMA-262 ShortCircuitExpression).
  MixedNullishLogicalOperators,
  /// Tagged template after optional chain (`?.`…`` ` ``) (ECMA-262 OptionalChain early error).
  OptionalChainTaggedTemplate,
  /// Bare `PrivateIdentifier` outside `#id in ShiftExpression` / member access
  /// (ECMA-262 RelationalExpression / PrimaryExpression).
  InvalidPrivateIdentifier,
  /// Bare `#` (PrivateIdentifier without IdentifierName). Mirrors tsc TS1127.
  InvalidCharacter,
  /// Junk token where a variable declarator was expected. Mirrors tsc TS1134.
  VariableDeclarationExpected,
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

#[cfg(feature = "diagnostics")]
impl ParseJsError for SyntaxError {
  fn to_diagnostic(&self, file: FileId) -> Diagnostic {
    SyntaxError::to_diagnostic(self, file)
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
      SyntaxErrorType::Cancelled => "PS0016",
      SyntaxErrorType::InvalidOptionalChainFromNew => "PS0017",
      SyntaxErrorType::DeclarationInSingleStatementPosition => "PS0018",
      SyntaxErrorType::BindingPatternRequiresInitializer => "PS0019",
      SyntaxErrorType::UnterminatedMultilineComment => "PS0020",
      SyntaxErrorType::InvalidRestParameter => "PS0021",
      SyntaxErrorType::NumericLiteralFollowedByIdentifier => "PS0022",
      SyntaxErrorType::HtmlCommentInModule => "PS0023",
      SyntaxErrorType::InvalidClassHeritage => "PS0024",
      SyntaxErrorType::LegacyOctalEscapeInTemplate => "PS0025",
      SyntaxErrorType::InvalidUpdateOperand => "PS0026",
      SyntaxErrorType::MixedNullishLogicalOperators => "PS0027",
      SyntaxErrorType::OptionalChainTaggedTemplate => "PS0028",
      SyntaxErrorType::InvalidPrivateIdentifier => "PS0029",
      SyntaxErrorType::InvalidCharacter => "PS0030",
      SyntaxErrorType::VariableDeclarationExpected => "PS0031",
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
      SyntaxErrorType::Cancelled => "parsing cancelled".into(),
      SyntaxErrorType::InvalidOptionalChainFromNew => {
        "invalid optional chain from new expression".into()
      }
      SyntaxErrorType::DeclarationInSingleStatementPosition => {
        "declaration not allowed in single-statement position".into()
      }
      SyntaxErrorType::BindingPatternRequiresInitializer => {
        "binding pattern requires an initializer".into()
      }
      SyntaxErrorType::UnterminatedMultilineComment => "unterminated multiline comment".into(),
      SyntaxErrorType::InvalidRestParameter => "invalid rest parameter".into(),
      SyntaxErrorType::NumericLiteralFollowedByIdentifier => {
        "numeric literal cannot be immediately followed by an identifier".into()
      }
      SyntaxErrorType::HtmlCommentInModule => {
        "HTML-like comments are not allowed in module code".into()
      }
      SyntaxErrorType::InvalidClassHeritage => {
        "class heritage must be a left-hand-side expression".into()
      }
      SyntaxErrorType::LegacyOctalEscapeInTemplate => {
        "octal escape sequences are not allowed in template literals".into()
      }
      SyntaxErrorType::InvalidUpdateOperand => "invalid operand of update expression".into(),
      SyntaxErrorType::MixedNullishLogicalOperators => {
        "nullish coalescing cannot be mixed with logical and/or without parentheses".into()
      }
      SyntaxErrorType::OptionalChainTaggedTemplate => {
        "tagged template cannot follow optional chain".into()
      }
      SyntaxErrorType::InvalidPrivateIdentifier => {
        "private identifier is only valid in member access or `#name in` expressions".into()
      }
      SyntaxErrorType::InvalidCharacter => "Invalid character.".into(),
      SyntaxErrorType::VariableDeclarationExpected => "Variable declaration expected.".into(),
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
