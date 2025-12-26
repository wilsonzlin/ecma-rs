use crate::char::is_line_terminator;
use crate::char::CharFilter;
use crate::char::DIGIT;
use crate::char::DIGIT_BIN;
use crate::char::DIGIT_HEX;
use crate::char::DIGIT_OCT;
use crate::char::ECMASCRIPT_LINE_TERMINATORS;
use crate::char::ECMASCRIPT_WHITESPACE;
use crate::loc::Loc;
use crate::token::keyword_from_str;
use crate::token::Token;
use crate::token::TT;
use crate::Dialect;
use ahash::HashMap;
use ahash::HashMapExt;
use aho_corasick::AhoCorasick;
use aho_corasick::AhoCorasickBuilder;
use aho_corasick::AhoCorasickKind;
use aho_corasick::Anchored;
use aho_corasick::Input;
use aho_corasick::MatchKind;
use aho_corasick::StartKind;
use core::ops::Index;
use memchr::memchr;
use memchr::memchr2;
use memchr::memchr3;
use once_cell::sync::Lazy;
use unicode_ident::is_xid_continue;
use unicode_ident::is_xid_start;

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum LexMode {
  JsxTag,
  JsxTextContent,
  SlashIsRegex,
  Standard,
  TemplateStrContinue,
}

#[derive(Copy, Clone)]
pub struct LexerCheckpoint {
  next: usize,
}

// Contains the match length.
#[derive(Copy, Clone)]
struct Match(usize);

impl Match {
  pub fn len(&self) -> usize {
    self.0
  }

  pub fn prefix(&self, n: usize) -> Match {
    debug_assert!(n <= self.len());
    Match(n)
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }
}

struct PatternMatcher {
  patterns: Vec<TT>,
  matcher: AhoCorasick,
  anchored: bool,
}

impl PatternMatcher {
  pub fn new<D: AsRef<str>>(anchored: bool, patterns: Vec<(TT, D)>) -> Self {
    let (tts, syns): (Vec<_>, Vec<_>) = patterns.into_iter().unzip();
    // Convert string patterns to byte patterns for AhoCorasick
    let byte_syns: Vec<Vec<u8>> = syns
      .iter()
      .map(|s| s.as_ref().as_bytes().to_vec())
      .collect();
    let matcher = AhoCorasickBuilder::new()
      .start_kind(if anchored {
        StartKind::Anchored
      } else {
        StartKind::Unanchored
      })
      .kind(Some(AhoCorasickKind::DFA))
      .match_kind(MatchKind::LeftmostLongest)
      .build(byte_syns)
      .unwrap();
    PatternMatcher {
      patterns: tts,
      matcher,
      anchored,
    }
  }

  pub fn find(&self, lexer: &Lexer) -> LexResult<(TT, Match)> {
    self
      .matcher
      .find(
        Input::new(&lexer.source[lexer.next..]).anchored(if self.anchored {
          Anchored::Yes
        } else {
          Anchored::No
        }),
      )
      .map(|m| (self.patterns[m.pattern().as_usize()], Match(m.end())))
      .ok_or_else(|| LexNotFound)
  }
}

#[derive(Debug)]
pub(crate) struct LexNotFound;

type LexResult<T> = Result<T, LexNotFound>;

pub struct Lexer<'a> {
  source: &'a str,
  next: usize,
}

impl<'a> Lexer<'a> {
  pub fn new(code: &'a str) -> Lexer<'a> {
    Lexer {
      source: code,
      next: 0,
    }
  }

  pub fn next(&self) -> usize {
    self.next
  }

  fn end(&self) -> usize {
    self.source.len()
  }

  fn remaining(&self) -> usize {
    self.end() - self.next
  }

  pub fn source_range(&self) -> Loc {
    Loc(0, self.end())
  }

  fn eof_range(&self) -> Loc {
    Loc(self.end(), self.end())
  }

  fn at_end(&self) -> bool {
    self.next >= self.end()
  }

  fn peek(&self, n: usize) -> LexResult<char> {
    self.peek_or_eof(n).ok_or_else(|| LexNotFound)
  }

  fn peek_or_eof(&self, n: usize) -> Option<char> {
    self.source[self.next..].chars().nth(n)
  }

  /// WARNING: Prefer checkpoints instead. Only use this if you know what you're doing.
  pub fn set_next(&mut self, next: usize) {
    self.next = next;
  }

  pub fn checkpoint(&self) -> LexerCheckpoint {
    LexerCheckpoint { next: self.next }
  }

  pub fn since_checkpoint(&self, checkpoint: LexerCheckpoint) -> Loc {
    Loc(checkpoint.next, self.next)
  }

  pub fn apply_checkpoint(&mut self, checkpoint: LexerCheckpoint) {
    self.next = checkpoint.next;
  }

  fn n(&self, n: usize) -> LexResult<Match> {
    if self.next + n > self.end() {
      return Err(LexNotFound);
    };
    Ok(Match(n))
  }

  fn if_char(&self, c: char) -> Match {
    let remaining = &self.source[self.next..];
    if let Some(first_char) = remaining.chars().next() {
      if first_char == c {
        return Match(c.len_utf8());
      }
    }
    Match(0)
  }

  fn through_char_or_end(&self, c: char) -> Match {
    if c.is_ascii() {
      memchr(c as u8, self.source[self.next..].as_bytes())
        .map(|pos| Match(pos + 1))
        .unwrap_or_else(|| Match(self.remaining()))
    } else {
      self.source[self.next..]
        .find(c)
        .map(|pos| Match(pos + c.len_utf8()))
        .unwrap_or_else(|| Match(self.remaining()))
    }
  }

  fn while_not_char(&self, a: char) -> Match {
    if a.is_ascii() {
      Match(memchr(a as u8, self.source[self.next..].as_bytes()).unwrap_or(self.remaining()))
    } else {
      Match(self.source[self.next..].find(a).unwrap_or(self.remaining()))
    }
  }

  fn while_not_2_chars(&self, a: char, b: char) -> Match {
    if a.is_ascii() && b.is_ascii() {
      Match(
        memchr2(a as u8, b as u8, self.source[self.next..].as_bytes()).unwrap_or(self.remaining()),
      )
    } else {
      let remaining = &self.source[self.next..];
      let pos_a = remaining.find(a);
      let pos_b = remaining.find(b);
      let pos = match (pos_a, pos_b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
      };
      Match(pos.unwrap_or(self.remaining()))
    }
  }

  fn while_not_3_chars(&self, a: char, b: char, c: char) -> Match {
    if a.is_ascii() && b.is_ascii() && c.is_ascii() {
      Match(
        memchr3(
          a as u8,
          b as u8,
          c as u8,
          self.source[self.next..].as_bytes(),
        )
        .unwrap_or(self.remaining()),
      )
    } else {
      let remaining = &self.source[self.next..];
      let pos_a = remaining.find(a);
      let pos_b = remaining.find(b);
      let pos_c = remaining.find(c);
      let pos = [pos_a, pos_b, pos_c].iter().filter_map(|&p| p).min();
      Match(pos.unwrap_or(self.remaining()))
    }
  }

  fn while_chars(&self, chars: &CharFilter) -> Match {
    let mut len = 0;
    for ch in self.source[self.next..].chars() {
      if chars.has(ch) {
        len += ch.len_utf8();
      } else {
        break;
      }
    }
    Match(len)
  }

  fn consume(&mut self, m: Match) -> Match {
    self.next += m.len();
    m
  }

  fn consume_next(&mut self) -> LexResult<char> {
    let c = self.peek(0)?;
    self.next += c.len_utf8();
    Ok(c)
  }

  fn skip_expect(&mut self, n: usize) {
    debug_assert!(self.next + n <= self.end());
    self.next += n;
  }

  fn drive_fallible(
    &mut self,
    preceded_by_line_terminator: bool,
    f: impl FnOnce(&mut Self) -> LexResult<TT>,
  ) -> Token {
    let cp = self.checkpoint();
    let typ = f(self).unwrap_or(TT::Invalid);
    Token {
      loc: self.since_checkpoint(cp),
      typ,
      preceded_by_line_terminator,
    }
  }

  fn drive(&mut self, preceded_by_line_terminator: bool, f: impl FnOnce(&mut Self) -> TT) -> Token {
    self.drive_fallible(preceded_by_line_terminator, |lexer| Ok(f(lexer)))
  }
}

impl<'a> Index<Loc> for Lexer<'a> {
  type Output = str;

  fn index(&self, index: Loc) -> &Self::Output {
    &self.source[index.0..index.1]
  }
}

impl<'a> Index<Match> for Lexer<'a> {
  type Output = str;

  fn index(&self, m: Match) -> &Self::Output {
    &self.source[self.next - m.len()..self.next]
  }
}

#[rustfmt::skip]
pub static OPERATORS_MAPPING: Lazy<HashMap<TT, &'static str>> = Lazy::new(|| {
  let mut map = HashMap::<TT, &'static str>::new();
  map.insert(TT::At, "@");
  map.insert(TT::Ampersand, "&");
  map.insert(TT::AmpersandAmpersand, "&&");
  map.insert(TT::AmpersandAmpersandEquals, "&&=");
  map.insert(TT::AmpersandEquals, "&=");
  map.insert(TT::Asterisk, "*");
  map.insert(TT::AsteriskAsterisk, "**");
  map.insert(TT::AsteriskAsteriskEquals, "**=");
  map.insert(TT::AsteriskEquals, "*=");
  map.insert(TT::Bar, "|");
  map.insert(TT::BarBar, "||");
  map.insert(TT::BarBarEquals, "||=");
  map.insert(TT::BarEquals, "|=");
  map.insert(TT::BraceClose, "}");
  map.insert(TT::BraceOpen, "{");
  map.insert(TT::BracketClose, "]");
  map.insert(TT::BracketOpen, "[");
  map.insert(TT::Caret, "^");
  map.insert(TT::CaretEquals, "^=");
  map.insert(TT::ChevronLeft, "<");
  map.insert(TT::ChevronLeftChevronLeft, "<<");
  map.insert(TT::ChevronLeftChevronLeftEquals, "<<=");
  map.insert(TT::ChevronLeftEquals, "<=");
  map.insert(TT::ChevronRight, ">");
  map.insert(TT::ChevronRightChevronRight, ">>");
  map.insert(TT::ChevronRightChevronRightChevronRight, ">>>");
  map.insert(TT::ChevronRightChevronRightChevronRightEquals, ">>>=");
  map.insert(TT::ChevronRightChevronRightEquals, ">>=");
  map.insert(TT::ChevronRightEquals, ">=");
  map.insert(TT::Colon, ":");
  map.insert(TT::Comma, ",");
  map.insert(TT::Dot, ".");
  map.insert(TT::DotDotDot, "...");
  map.insert(TT::Equals, "=");
  map.insert(TT::EqualsChevronRight, "=>");
  map.insert(TT::EqualsEquals, "==");
  map.insert(TT::EqualsEqualsEquals, "===");
  map.insert(TT::Exclamation, "!");
  map.insert(TT::ExclamationEquals, "!=");
  map.insert(TT::ExclamationEqualsEquals, "!==");
  map.insert(TT::Hyphen, "-");
  map.insert(TT::HyphenEquals, "-=");
  map.insert(TT::HyphenHyphen, "--");
  map.insert(TT::ParenthesisClose, ")");
  map.insert(TT::ParenthesisOpen, "(");
  map.insert(TT::Percent, "%");
  map.insert(TT::PercentEquals, "%=");
  map.insert(TT::Plus, "+");
  map.insert(TT::PlusEquals, "+=");
  map.insert(TT::PlusPlus, "++");
  map.insert(TT::PrivateMember, "#");
  map.insert(TT::Question, "?");
  map.insert(TT::QuestionDot, "?.");
  map.insert(TT::QuestionDotBracketOpen, "?.[");
  map.insert(TT::QuestionDotParenthesisOpen, "?.(");
  map.insert(TT::QuestionQuestion, "??");
  map.insert(TT::QuestionQuestionEquals, "??=");
  map.insert(TT::Semicolon, ";");
  map.insert(TT::Slash, "/");
  map.insert(TT::SlashEquals, "/=");
  map.insert(TT::Tilde, "~");
  map
});

pub static KEYWORDS_MAPPING: Lazy<HashMap<TT, &'static str>> = Lazy::new(|| {
  let mut map = HashMap::<TT, &'static str>::new();
  map.insert(TT::KeywordAs, "as");
  map.insert(TT::KeywordAsync, "async");
  map.insert(TT::KeywordAwait, "await");
  map.insert(TT::KeywordBreak, "break");
  map.insert(TT::KeywordCase, "case");
  map.insert(TT::KeywordCatch, "catch");
  map.insert(TT::KeywordClass, "class");
  map.insert(TT::KeywordConst, "const");
  map.insert(TT::KeywordConstructor, "constructor");
  map.insert(TT::KeywordContinue, "continue");
  map.insert(TT::KeywordDebugger, "debugger");
  map.insert(TT::KeywordDefault, "default");
  map.insert(TT::KeywordDelete, "delete");
  map.insert(TT::KeywordDo, "do");
  map.insert(TT::KeywordElse, "else");
  map.insert(TT::KeywordEnum, "enum");
  map.insert(TT::KeywordExport, "export");
  map.insert(TT::KeywordExtends, "extends");
  map.insert(TT::KeywordFinally, "finally");
  map.insert(TT::KeywordFor, "for");
  map.insert(TT::KeywordFrom, "from");
  map.insert(TT::KeywordFunction, "function");
  map.insert(TT::KeywordGet, "get");
  map.insert(TT::KeywordIf, "if");
  map.insert(TT::KeywordImport, "import");
  map.insert(TT::KeywordIn, "in");
  map.insert(TT::KeywordInstanceof, "instanceof");
  map.insert(TT::KeywordLet, "let");
  map.insert(TT::KeywordNew, "new");
  map.insert(TT::KeywordOf, "of");
  map.insert(TT::KeywordOut, "out");
  map.insert(TT::KeywordReturn, "return");
  map.insert(TT::KeywordSet, "set");
  map.insert(TT::KeywordStatic, "static");
  map.insert(TT::KeywordSuper, "super");
  map.insert(TT::KeywordSwitch, "switch");
  map.insert(TT::KeywordThis, "this");
  map.insert(TT::KeywordThrow, "throw");
  map.insert(TT::KeywordTry, "try");
  map.insert(TT::KeywordTypeof, "typeof");
  map.insert(TT::KeywordUsing, "using");
  map.insert(TT::KeywordVar, "var");
  map.insert(TT::KeywordVoid, "void");
  map.insert(TT::KeywordWhile, "while");
  map.insert(TT::KeywordWith, "with");
  map.insert(TT::KeywordYield, "yield");
  // TypeScript keywords
  map.insert(TT::KeywordAbstract, "abstract");
  map.insert(TT::KeywordAccessor, "accessor");
  map.insert(TT::KeywordAny, "any");
  map.insert(TT::KeywordAsserts, "asserts");
  map.insert(TT::KeywordBigIntType, "bigint");
  map.insert(TT::KeywordBooleanType, "boolean");
  map.insert(TT::KeywordDeclare, "declare");
  map.insert(TT::KeywordImplements, "implements");
  map.insert(TT::KeywordInfer, "infer");
  map.insert(TT::KeywordInterface, "interface");
  map.insert(TT::KeywordIs, "is");
  map.insert(TT::KeywordKeyof, "keyof");
  map.insert(TT::KeywordModule, "module");
  map.insert(TT::KeywordNamespace, "namespace");
  map.insert(TT::KeywordNever, "never");
  map.insert(TT::KeywordNumberType, "number");
  map.insert(TT::KeywordObjectType, "object");
  map.insert(TT::KeywordOverride, "override");
  map.insert(TT::KeywordPrivate, "private");
  map.insert(TT::KeywordProtected, "protected");
  map.insert(TT::KeywordPublic, "public");
  map.insert(TT::KeywordReadonly, "readonly");
  map.insert(TT::KeywordSatisfies, "satisfies");
  map.insert(TT::KeywordStringType, "string");
  map.insert(TT::KeywordSymbolType, "symbol");
  map.insert(TT::KeywordType, "type");
  map.insert(TT::KeywordUndefinedType, "undefined");
  map.insert(TT::KeywordUnique, "unique");
  map.insert(TT::KeywordUnknown, "unknown");
  map.insert(TT::LiteralFalse, "false");
  map.insert(TT::LiteralNull, "null");
  map.insert(TT::LiteralTrue, "true");
  map
});

#[rustfmt::skip]
static SIG: Lazy<PatternMatcher> = Lazy::new(|| {
  let mut patterns: Vec<(TT, String)> = Vec::new();
  for (&k, &v) in OPERATORS_MAPPING.iter() {
    patterns.push((k, v.into()));
  }
  for c in "0123456789".chars() {
    patterns.push((TT::LiteralNumber, c.to_string()));
  }
  patterns.push((TT::LiteralNumberBin, "0b".into()));
  patterns.push((TT::LiteralNumberBin, "0B".into()));
  patterns.push((TT::LiteralNumberHex, "0x".into()));
  patterns.push((TT::LiteralNumberHex, "0X".into()));
  patterns.push((TT::LiteralNumberOct, "0o".into()));
  patterns.push((TT::LiteralNumberOct, "0O".into()));
  // Prevent `.` immediately followed by a digit from being recognised as the `.` operator.
  for digit in '0'..='9' {
    patterns.push((TT::LiteralNumber, format!(".{}", digit)));
  }
  // Prevent `?` immediately followed by a decimal number from being recognised as the `?.` operator.
  for digit in '0'..='9' {
    patterns.push((TT::Question, format!("?.{}", digit)));
  }
  patterns.push((TT::ChevronLeftSlash, "</".into()));
  patterns.push((TT::LiteralString, "\"".into()));
  patterns.push((TT::LiteralString, "'".into()));
  patterns.push((TT::LiteralTemplatePartString, "`".into()));

  PatternMatcher::new(true, patterns)
});

static ML_COMMENT: Lazy<PatternMatcher> = Lazy::new(|| {
  let mut patterns: Vec<(TT, String)> = vec![(TT::CommentMultilineEnd, "*/".into())];
  // Always match CRLF as a single line terminator if present.
  patterns.push((TT::LineTerminator, "\r\n".into()));
  for terminator in ECMASCRIPT_LINE_TERMINATORS {
    patterns.push((TT::LineTerminator, terminator.to_string()));
  }
  PatternMatcher::new(false, patterns)
});

static INSIG: Lazy<PatternMatcher> = Lazy::new(|| {
  let mut patterns: Vec<(TT, String)> = Vec::new();
  // Match CRLF as a single line terminator when present.
  patterns.push((TT::LineTerminator, "\r\n".into()));
  for terminator in ECMASCRIPT_LINE_TERMINATORS {
    patterns.push((TT::LineTerminator, terminator.to_string()));
  }
  for whitespace in ECMASCRIPT_WHITESPACE {
    patterns.push((TT::Whitespace, whitespace.to_string()));
  }
  patterns.extend(
    [
      (TT::CommentMultiline, "/*".into()),
      (TT::CommentSingle, "//".into()),
      (TT::CommentSingle, "<!--".into()),
      (TT::CommentSingle, "-->".into()),
    ]
    .into_iter(),
  );
  PatternMatcher::new(true, patterns)
});

fn find_line_terminator(text: &str) -> Option<(usize, usize)> {
  let mut earliest: Option<(usize, char)> = None;
  for terminator in ECMASCRIPT_LINE_TERMINATORS {
    if let Some(pos) = text.find(terminator) {
      if earliest.map_or(true, |(earliest_pos, _)| pos < earliest_pos) {
        earliest = Some((pos, terminator));
      }
    }
  }
  earliest.map(|(pos, terminator)| {
    let len = if terminator == '\r' && text.as_bytes().get(pos + 1) == Some(&b'\n') {
      2
    } else {
      terminator.len_utf8()
    };
    (pos, len)
  })
}

/// Returns whether the comment includes a line terminator.
fn lex_multiline_comment(lexer: &mut Lexer<'_>) -> bool {
  // Consume `/*`.
  lexer.skip_expect(2);
  let mut contains_newline = false;
  loop {
    let (tt, mat) = ML_COMMENT
      .find(lexer)
      // We can't reject with an error, so we just consume the rest of the source code if no matching `*/` is found.
      .unwrap_or_else(|_| (TT::EOF, Match(lexer.remaining())));
    lexer.consume(mat);
    match tt {
      TT::CommentMultilineEnd | TT::EOF => {
        break;
      }
      TT::LineTerminator => {
        contains_newline = true;
      }
      _ => unreachable!(),
    };
  }
  contains_newline
}

fn lex_single_comment(lexer: &mut Lexer<'_>, prefix: Match) -> bool {
  // Consume the comment prefix (//, <!--, or -->).
  lexer.skip_expect(prefix.len());
  if let Some((offset, terminator_len)) = find_line_terminator(&lexer.source[lexer.next..]) {
    lexer.skip_expect(offset + terminator_len);
    true
  } else {
    lexer.skip_expect(lexer.remaining());
    false
  }
}

fn is_identifier_start(c: char) -> bool {
  if c.is_ascii() {
    matches!(c, '$' | '_' | 'a'..='z' | 'A'..='Z')
  } else {
    is_xid_start(c)
  }
}

fn is_identifier_continue(c: char, mode: LexMode) -> bool {
  if c.is_ascii() {
    if mode == LexMode::JsxTag && c == '-' {
      return true;
    }
    matches!(c, '$' | '_' | '0'..='9' | 'a'..='z' | 'A'..='Z')
  } else {
    is_xid_continue(c) || c == '\u{200c}' || c == '\u{200d}'
  }
}

#[derive(Default)]
struct IdentifierLexResult {
  had_escape: bool,
}

fn lex_unicode_escape(lexer: &mut Lexer<'_>) -> LexResult<char> {
  // We're at '\', consume it
  lexer.skip_expect(1);
  // Expect 'u'
  if lexer.peek(0)? != 'u' {
    return Err(LexNotFound);
  }
  lexer.skip_expect(1);

  // Check for \u{...} or \uXXXX
  let value = if lexer.peek_or_eof(0) == Some('{') {
    lexer.skip_expect(1);
    let checkpoint = lexer.checkpoint();
    lexer.consume(lexer.while_chars(&DIGIT_HEX));
    let consumed = lexer.next() - checkpoint.next;
    if consumed == 0 {
      return Err(LexNotFound);
    }
    let digits = lexer[lexer.since_checkpoint(checkpoint)].to_string();
    if lexer.peek(0)? != '}' {
      return Err(LexNotFound);
    }
    lexer.skip_expect(1);
    u32::from_str_radix(&digits, 16).ok()
  } else {
    let mut value = 0;
    for _ in 0..4 {
      let c = lexer.peek(0)?;
      if !DIGIT_HEX.has(c) {
        return Err(LexNotFound);
      }
      value = (value << 4) | c.to_digit(16).unwrap();
      lexer.skip_expect(1);
    }
    Some(value)
  };

  value.and_then(char::from_u32).ok_or(LexNotFound)
}

fn consume_identifier(lexer: &mut Lexer<'_>, mode: LexMode) -> LexResult<IdentifierLexResult> {
  let mut result = IdentifierLexResult::default();
  let starter = lexer.peek(0)?;
  if starter == '\\' {
    let c = lex_unicode_escape(lexer)?;
    result.had_escape = true;
    if !is_identifier_start(c) {
      return Err(LexNotFound);
    }
  } else if is_identifier_start(starter) {
    lexer.skip_expect(starter.len_utf8());
  } else {
    return Err(LexNotFound);
  }

  loop {
    match lexer.peek_or_eof(0) {
      Some('\\') => {
        let c = lex_unicode_escape(lexer)?;
        result.had_escape = true;
        if !is_identifier_continue(c, mode) {
          return Err(LexNotFound);
        }
      }
      Some(c) if is_identifier_continue(c, mode) => {
        lexer.skip_expect(c.len_utf8());
      }
      _ => break,
    }
  }

  Ok(result)
}

fn lex_identifier(lexer: &mut Lexer<'_>, mode: LexMode) -> LexResult<TT> {
  let start = lexer.next();
  let result = consume_identifier(lexer, mode)?;

  if !result.had_escape {
    let ident = &lexer[Loc(start, lexer.next())];
    if ident.is_ascii() {
      if let Some(keyword) = keyword_from_str(ident) {
        return Ok(keyword);
      }
    }
  }

  Ok(TT::Identifier)
}

fn consume_identifier_parts(lexer: &mut Lexer<'_>, mode: LexMode) -> LexResult<()> {
  loop {
    match lexer.peek_or_eof(0) {
      Some('\\') => {
        let c = lex_unicode_escape(lexer)?;
        if !is_identifier_continue(c, mode) {
          return Err(LexNotFound);
        }
      }
      Some(c) if is_identifier_continue(c, mode) => {
        lexer.skip_expect(c.len_utf8());
      }
      _ => break,
    }
  }
  Ok(())
}

/// Consume digits with numeric separators (_)
/// ES2021 allows underscores as separators: 1_000_000
fn consume_digits_with_separators(
  lexer: &mut Lexer<'_>,
  digit_filter: &CharFilter,
) -> (bool, bool) {
  let mut consumed_digit = false;
  let mut valid = true;
  let mut prev_sep = false;

  loop {
    match lexer.peek_or_eof(0) {
      Some('_') => {
        // Separators must be surrounded by digits.
        let has_following_digit = lexer.peek_or_eof(1).map_or(false, |c| digit_filter.has(c));
        if prev_sep || !consumed_digit || !has_following_digit {
          valid = false;
        }
        lexer.skip_expect(1);
        prev_sep = true;
      }
      Some(c) if digit_filter.has(c) => {
        consumed_digit = true;
        prev_sep = false;
        lexer.skip_expect(c.len_utf8());
      }
      _ => break,
    }
  }

  if prev_sep {
    valid = false;
  }

  (consumed_digit, valid)
}

fn lex_bigint_or_number(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  let start_pos = lexer.next();
  let mut valid = true;
  let first_char = lexer.peek(0)?;
  let mut integer_end = start_pos;

  // Integer part (may be empty for leading-dot literals)
  let has_integer = if first_char != '.' {
    let (digits, ok) = consume_digits_with_separators(lexer, &DIGIT);
    valid &= ok && digits;
    integer_end = lexer.next();
    digits
  } else {
    false
  };

  let integer_part = &lexer[Loc(start_pos, integer_end)];
  let is_legacy_octal = has_integer
    && integer_part.starts_with('0')
    && integer_part.len() > 1
    && integer_part
      .chars()
      .filter(|c| *c != '_')
      .all(|c| matches!(c, '0'..='7'));

  // BigInt suffix (only allowed for integer literals)
  if lexer.peek_or_eof(0) == Some('n') && first_char != '.' {
    if integer_part.len() > 1 && first_char == '0' {
      valid = false;
    }
    lexer.skip_expect(1);
    return Ok(if valid {
      TT::LiteralBigInt
    } else {
      TT::Invalid
    });
  }

  // Fractional part
  if lexer.peek_or_eof(0) == Some('.') && !is_legacy_octal {
    lexer.consume(lexer.if_char('.'));
    let (digits, ok) = consume_digits_with_separators(lexer, &DIGIT);
    valid &= ok;
    if !has_integer && !digits {
      valid = false;
    }
  }

  // Exponent
  if matches!(lexer.peek_or_eof(0), Some('e' | 'E')) {
    lexer.skip_expect(1);
    if matches!(lexer.peek_or_eof(0), Some('+' | '-')) {
      lexer.skip_expect(1);
    }
    let (digits, ok) = consume_digits_with_separators(lexer, &DIGIT);
    valid &= ok && digits;
  }

  Ok(if valid {
    TT::LiteralNumber
  } else {
    TT::Invalid
  })
}

fn lex_binary_bigint_or_number(lexer: &mut Lexer<'_>) -> TT {
  lexer.skip_expect(2);
  let (has_digits, valid_digits) = consume_digits_with_separators(lexer, &DIGIT_BIN);
  let mut valid = valid_digits && has_digits;

  // Consume any remaining decimal digits (which are invalid for binary) and separators after them
  let invalid_start = lexer.next();
  let (_, extra_valid) = consume_digits_with_separators(lexer, &DIGIT);
  let has_invalid_digits = lexer.next() > invalid_start;
  valid &= extra_valid && !has_invalid_digits;

  let is_bigint = !lexer.consume(lexer.if_char('n')).is_empty();

  if !valid {
    return TT::Invalid;
  }

  if is_bigint {
    TT::LiteralBigInt
  } else {
    TT::LiteralNumber
  }
}

fn lex_hex_bigint_or_number(lexer: &mut Lexer<'_>) -> TT {
  lexer.skip_expect(2);
  let (has_digits, valid_digits) = consume_digits_with_separators(lexer, &DIGIT_HEX);
  let is_bigint = !lexer.consume(lexer.if_char('n')).is_empty();
  if has_digits && valid_digits {
    if is_bigint {
      TT::LiteralBigInt
    } else {
      TT::LiteralNumber
    }
  } else {
    TT::Invalid
  }
}

fn lex_oct_bigint_or_number(lexer: &mut Lexer<'_>) -> TT {
  lexer.skip_expect(2);
  let (has_digits, valid_digits) = consume_digits_with_separators(lexer, &DIGIT_OCT);
  let invalid_start = lexer.next();
  let (_, extra_valid) = consume_digits_with_separators(lexer, &DIGIT);
  let has_invalid_digits = lexer.next() > invalid_start;
  let is_bigint = !lexer.consume(lexer.if_char('n')).is_empty();

  if has_digits && valid_digits && extra_valid && !has_invalid_digits {
    if is_bigint {
      TT::LiteralBigInt
    } else {
      TT::LiteralNumber
    }
  } else {
    TT::Invalid
  }
}

fn lex_private_member(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  // Include the `#` in the token.
  lexer.skip_expect(1);
  consume_identifier(lexer, LexMode::Standard)?;
  Ok(TT::PrivateMember)
}

fn lex_regex(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  // Consume slash.
  lexer.consume(lexer.n(1)?);
  let mut in_charset = false;
  loop {
    match lexer.consume_next()? {
      '\\' => {
        // Cannot escape line terminator.
        let escaped_char = lexer.peek(0)?;
        if is_line_terminator(escaped_char) {
          return Ok(TT::Invalid);
        };
        lexer.skip_expect(escaped_char.len_utf8());
      }
      '/' if !in_charset => {
        break;
      }
      '[' => {
        in_charset = true;
      }
      ']' if in_charset => {
        in_charset = false;
      }
      c if is_line_terminator(c) => {
        return Ok(TT::Invalid);
      }
      _ => {}
    };
  }
  consume_identifier_parts(lexer, LexMode::Standard)?;
  Ok(TT::LiteralRegex)
}

fn lex_string(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  let quote = lexer.consume_next()?;
  let mut invalid = false;
  loop {
    // Consume everything up to an escape, a line terminator, or the closing quote.
    let mut m = lexer.while_not_3_chars('\\', '\r', quote);
    let newline = lexer.while_not_char('\n');
    if newline.len() < m.len() {
      m = newline;
    }
    let line_sep = lexer.while_not_char('\u{2028}');
    if line_sep.len() < m.len() {
      m = line_sep;
    }
    let para_sep = lexer.while_not_char('\u{2029}');
    if para_sep.len() < m.len() {
      m = para_sep;
    }
    lexer.consume(m);

    let c = lexer.peek(0)?;
    match c {
      '\\' => {
        // Escape sequence (including line continuations).
        lexer.skip_expect(1);
        match lexer.peek_or_eof(0) {
          Some('\r') => {
            lexer.skip_expect(1);
            if lexer.peek_or_eof(0) == Some('\n') {
              lexer.skip_expect(1);
            }
          }
          Some(next_char @ ('\n' | '\u{2028}' | '\u{2029}')) => {
            // Line continuation.
            lexer.skip_expect(next_char.len_utf8());
          }
          Some(next_char) => {
            lexer.skip_expect(next_char.len_utf8());
          }
          None => {}
        };
      }
      '\r' => {
        invalid = true;
        lexer.skip_expect(1);
        if lexer.peek_or_eof(0) == Some('\n') {
          lexer.skip_expect(1);
        }
      }
      '\n' | '\u{2028}' | '\u{2029}' => {
        invalid = true;
        lexer.skip_expect(c.len_utf8());
      }
      c if c == quote => {
        lexer.skip_expect(c.len_utf8());
        break;
      }
      _ => unreachable!(),
    };
  }
  Ok(if invalid {
    TT::Invalid
  } else {
    TT::LiteralString
  })
}

fn lex_jsx_string(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  let quote = lexer.consume_next()?;
  loop {
    lexer.consume(lexer.while_not_char(quote));
    match lexer.peek_or_eof(0) {
      Some(c) if c == quote => {
        lexer.skip_expect(c.len_utf8());
        return Ok(TT::LiteralString);
      }
      Some(_) => {
        lexer.skip_expect(1);
      }
      None => return Err(LexNotFound),
    }
  }
}

/// Ends with `${` or backtick.
pub(crate) fn lex_template_string_continue(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  let mut ended = false;
  loop {
    lexer.consume(lexer.while_not_3_chars('\\', '`', '$'));
    // Check for EOF (unterminated template string)
    if lexer.remaining() == 0 {
      // Return error for unterminated template - will become TT::Invalid
      return Err(LexNotFound);
    }
    match lexer.peek(0)? {
      '\\' => {
        // Consume the backslash
        lexer.skip_expect(1);
        // Consume the next character (which may be multi-byte UTF-8)
        if let Ok(next_char) = lexer.peek(0) {
          lexer.skip_expect(next_char.len_utf8());
        }
      }
      '`' => {
        ended = true;
        lexer.skip_expect(1);
        break;
      }
      '$' => {
        if lexer.peek(1)? == '{' {
          lexer.skip_expect(2);
          break;
        } else {
          lexer.skip_expect(1);
        }
      }
      _ => unreachable!(),
    };
  }
  let typ = if ended {
    TT::LiteralTemplatePartStringEnd
  } else {
    TT::LiteralTemplatePartString
  };
  Ok(typ)
}

fn lex_template(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  // Consume backtick.
  lexer.skip_expect(1);
  lex_template_string_continue(lexer)
}

fn is_ts_only_keyword(tt: TT) -> bool {
  matches!(
    tt,
    TT::KeywordAbstract
      | TT::KeywordAccessor
      | TT::KeywordAny
      | TT::KeywordAsserts
      | TT::KeywordBigIntType
      | TT::KeywordBooleanType
      | TT::KeywordDeclare
      | TT::KeywordImplements
      | TT::KeywordInfer
      | TT::KeywordInterface
      | TT::KeywordIs
      | TT::KeywordKeyof
      | TT::KeywordModule
      | TT::KeywordNamespace
      | TT::KeywordNever
      | TT::KeywordNumberType
      | TT::KeywordObjectType
      | TT::KeywordPrivate
      | TT::KeywordProtected
      | TT::KeywordPublic
      | TT::KeywordReadonly
      | TT::KeywordSatisfies
      | TT::KeywordStringType
      | TT::KeywordSymbolType
      | TT::KeywordType
      | TT::KeywordUndefinedType
      | TT::KeywordUnique
      | TT::KeywordUnknown
      | TT::KeywordOut
  )
}

pub fn lex_next(lexer: &mut Lexer<'_>, mode: LexMode, dialect: Dialect) -> Token {
  if mode == LexMode::JsxTextContent {
    return lexer.drive(false, |lexer| {
      let mut len = 0;
      for ch in lexer.source[lexer.next..].chars() {
        if matches!(ch, '{' | '<') {
          break;
        }
        len += ch.len_utf8();
      }
      lexer.consume(Match(len));
      TT::JsxTextContent
    });
  };

  if mode == LexMode::TemplateStrContinue {
    return lexer.drive_fallible(false, |lexer| lex_template_string_continue(lexer));
  };

  // Skip whitespace and comments before the next significant token.
  // Track whether we're at the start of a line. We're at line start if:
  // 1. We're at the very beginning of the source (position 0), OR
  // 2. We encounter a line terminator in the INSIG loop
  // Initially, we're only at line start if we're at position 0.
  let mut at_line_start = lexer.next() == 0;
  let mut preceded_by_line_terminator = false;
  while let Ok((tt, mat)) = INSIG.find(&lexer) {
    // Special case: --> is only a comment at the start of a line
    // --> has length 3, check if it's at the start of a line
    if tt == TT::CommentSingle && mat.len() == 3 && !at_line_start {
      // Not at start of line, so don't treat as comment - break out
      break;
    }
    match tt {
      TT::LineTerminator => {
        lexer.consume(mat);
        at_line_start = true;
        preceded_by_line_terminator = true;
      }
      TT::Whitespace => {
        lexer.consume(mat);
        // Whitespace doesn't change whether we're at line start
      }
      TT::CommentMultiline => {
        let comment_has_line_terminator = lex_multiline_comment(lexer);
        // Multiline comments are insignificant for determining line start.
        // Only update at_line_start if the comment contains a line terminator.
        if comment_has_line_terminator {
          at_line_start = true;
        }
        preceded_by_line_terminator |= comment_has_line_terminator;
      }
      TT::CommentSingle => {
        let comment_has_line_terminator = lex_single_comment(lexer, mat);
        at_line_start |= comment_has_line_terminator;
        preceded_by_line_terminator |= comment_has_line_terminator;
      }
      _ => unreachable!(),
    };
  }

  // EOF is different from Invalid, so we should emit this specifically instead of letting drive_fallible return an Invalid.
  if lexer.at_end() {
    return Token {
      loc: lexer.eof_range(),
      typ: TT::EOF,
      preceded_by_line_terminator,
    };
  };

  let mut token = lexer.drive_fallible(preceded_by_line_terminator, |lexer| {
    if mode == LexMode::JsxTag {
      // In JSX tag context, treat consecutive '>' characters as separate tokens so
      // `></div>` doesn't get lexed as a single shift operator.
      if !lexer.if_char('>').is_empty() {
        lexer.consume(lexer.if_char('>'));
        return Ok(TT::ChevronRight);
      }
    }

    if let Some(c) = lexer.peek_or_eof(0) {
      if c == '\\' || is_identifier_start(c) {
        return lex_identifier(lexer, mode);
      }
    }

    SIG
      .find(lexer)
      .and_then(|(tt, mut mat)| match tt {
        TT::LiteralNumber => lex_bigint_or_number(lexer),
        TT::LiteralNumberBin => Ok(lex_binary_bigint_or_number(lexer)),
        TT::LiteralNumberHex => Ok(lex_hex_bigint_or_number(lexer)),
        TT::LiteralNumberOct => Ok(lex_oct_bigint_or_number(lexer)),
        TT::LiteralString if mode == LexMode::JsxTag => lex_jsx_string(lexer),
        TT::LiteralString => lex_string(lexer),
        TT::LiteralTemplatePartString => lex_template(lexer),
        TT::PrivateMember => lex_private_member(lexer),
        TT::Slash | TT::SlashEquals if mode == LexMode::SlashIsRegex => lex_regex(lexer),
        typ => {
          if typ == TT::Question && mat.len() != 1 {
            // We've matched `?.[0-9]`.
            mat = mat.prefix(1);
          };
          lexer.consume(mat);
          Ok(typ)
        }
      })
      .or_else(|_| {
        lexer.consume_next()?;
        Err(LexNotFound)
      })
  });

  if matches!(dialect, Dialect::Js | Dialect::Jsx) && is_ts_only_keyword(token.typ) {
    token.typ = TT::Identifier;
  }

  token
}
