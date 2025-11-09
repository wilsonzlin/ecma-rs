use crate::char::CharFilter;
use crate::char::DIGIT;
use crate::char::DIGIT_BIN;
use crate::char::DIGIT_HEX;
use crate::char::DIGIT_OCT;
use crate::char::ID_CONTINUE;
use crate::char::ID_CONTINUE_CHARSTR;
use crate::char::ID_CONTINUE_JSX;
use crate::char::ID_START;
use crate::char::ID_START_CHARSTR;
use crate::loc::Loc;
use crate::token::Token;
use crate::token::TT;
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
    let byte_syns: Vec<Vec<u8>> = syns.iter().map(|s| s.as_ref().as_bytes().to_vec()).collect();
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
      .find(Input::new(&lexer.source[lexer.next..]).anchored(if self.anchored {
        Anchored::Yes
      } else {
        Anchored::No
      }))
      .map(|m| (
        self.patterns[m.pattern().as_usize()],
        Match(m.end()),
      ))
      .ok_or_else(|| LexNotFound)
  }
}

#[derive(Debug)]
struct LexNotFound;

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
    self
      .peek_or_eof(n)
      .ok_or_else(|| LexNotFound)
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

  fn through_char(&self, c: char) -> LexResult<Match> {
    if c.is_ascii() {
      memchr(c as u8, self.source[self.next..].as_bytes())
        .map(|pos| Match(pos + 1))
        .ok_or_else(|| LexNotFound)
    } else {
      self.source[self.next..]
        .find(c)
        .map(|pos| Match(pos + c.len_utf8()))
        .ok_or_else(|| LexNotFound)
    }
  }

  fn while_not_char(&self, a: char) -> Match {
    if a.is_ascii() {
      Match(
        memchr(a as u8, self.source[self.next..].as_bytes()).unwrap_or(self.remaining()),
      )
    } else {
      Match(
        self.source[self.next..].find(a).unwrap_or(self.remaining()),
      )
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
        memchr3(a as u8, b as u8, c as u8, self.source[self.next..].as_bytes()).unwrap_or(self.remaining()),
      )
    } else {
      let remaining = &self.source[self.next..];
      let pos_a = remaining.find(a);
      let pos_b = remaining.find(b);
      let pos_c = remaining.find(c);
      let pos = [pos_a, pos_b, pos_c]
        .iter()
        .filter_map(|&p| p)
        .min();
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

  fn range(&self, m: Match) -> Loc {
    Loc(self.next, self.next + m.len())
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

  fn drive_fallible(&mut self, preceded_by_line_terminator: bool, f: impl FnOnce(&mut Self) -> LexResult<TT>) -> Token {
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
  map.insert(TT::KeywordReturn, "return");
  map.insert(TT::KeywordSet, "set");
  map.insert(TT::KeywordStatic, "static");
  map.insert(TT::KeywordSuper, "super");
  map.insert(TT::KeywordSwitch, "switch");
  map.insert(TT::KeywordThis, "this");
  map.insert(TT::KeywordThrow, "throw");
  map.insert(TT::KeywordTry, "try");
  map.insert(TT::KeywordTypeof, "typeof");
  map.insert(TT::KeywordVar, "var");
  map.insert(TT::KeywordVoid, "void");
  map.insert(TT::KeywordWhile, "while");
  map.insert(TT::KeywordWith, "with");
  map.insert(TT::KeywordYield, "yield");
  map.insert(TT::LiteralFalse, "false");
  map.insert(TT::LiteralNull, "null");
  map.insert(TT::LiteralTrue, "true");
  map
});

pub static KEYWORD_STRS: Lazy<HashMap<&'static str, usize>> = Lazy::new(|| {
  HashMap::<&'static str, usize>::from_iter(
    KEYWORDS_MAPPING.values().enumerate().map(|(i, v)| (*v, i)),
  )
});

#[rustfmt::skip]
static SIG: Lazy<PatternMatcher> = Lazy::new(|| {
  let mut patterns: Vec<(TT, String)> = Vec::new();
  for (&k, &v) in OPERATORS_MAPPING.iter() {
    patterns.push((k, v.into()));
  }
  for (&k, &v) in KEYWORDS_MAPPING.iter() {
    patterns.push((k, v.into()));
    // Avoid accidentally matching an identifier starting with a keyword as a keyword.
    for c in ID_CONTINUE_CHARSTR.chars() {
      let mut v = v.to_string();
      v.push(c);
      if !KEYWORD_STRS.contains_key(v.as_str()) {
        patterns.push((TT::Identifier, v));
      }
    }
  }
  // Add ASCII identifier start characters
  for c in ID_START_CHARSTR.chars() {
    patterns.push((TT::Identifier, c.to_string()));
  }
  // Add backslash for Unicode escapes in identifiers
  patterns.push((TT::Identifier, "\\".into()));
  // Add UTF-8 multi-byte sequences (for Unicode identifiers)
  // We detect the start of UTF-8 sequences by their byte patterns
  for b in 0..256u32 {
    if b >> 5 == 0b110 || b >> 4 == 0b1110 || b >> 3 == 0b11110 {
      if let Some(c) = char::from_u32(b) {
        patterns.push((TT::Identifier, c.to_string()));
      }
    }
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
  PatternMatcher::new::<&str>(false, vec![
    (TT::CommentMultilineEnd, "*/"),
    // WARNING: Does not consider Unicode whitespace allowed by spec.
    (TT::LineTerminator, "\r"),
    (TT::LineTerminator, "\n"),
  ])
});

static INSIG: Lazy<PatternMatcher> = Lazy::new(|| {
  PatternMatcher::new::<&str>(
    true,
    vec![
      (TT::LineTerminator, "\r"),
      (TT::LineTerminator, "\n"),
      (TT::Whitespace, "\x09"),
      (TT::Whitespace, "\x0b"),
      (TT::Whitespace, "\x0c"),
      (TT::Whitespace, "\x20"),
      // Unicode whitespace
      (TT::Whitespace, "\u{00A0}"),
      (TT::Whitespace, "\u{1680}"),
      (TT::Whitespace, "\u{2000}"),
      (TT::Whitespace, "\u{2001}"),
      (TT::Whitespace, "\u{2002}"),
      (TT::Whitespace, "\u{2003}"),
      (TT::Whitespace, "\u{2004}"),
      (TT::Whitespace, "\u{2005}"),
      (TT::Whitespace, "\u{2006}"),
      (TT::Whitespace, "\u{2007}"),
      (TT::Whitespace, "\u{2008}"),
      (TT::Whitespace, "\u{2009}"),
      (TT::Whitespace, "\u{200A}"),
      (TT::Whitespace, "\u{202F}"),
      (TT::Whitespace, "\u{205F}"),
      (TT::Whitespace, "\u{3000}"),
      (TT::Whitespace, "\u{FEFF}"),
      (TT::CommentMultiline, "/*"),
      (TT::CommentSingle, "//"),
      (TT::CommentSingle, "<!--"),
      (TT::CommentSingle, "-->"),
    ],
  )
});

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
  };
  contains_newline
}

fn lex_single_comment(lexer: &mut Lexer<'_>, prefix: Match) {
  // Consume the comment prefix (//, <!--, or -->).
  lexer.skip_expect(prefix.len());
  // WARNING: Does not consider other line terminators allowed by spec.
  lexer.consume(lexer.through_char_or_end('\n'));
}

fn lex_unicode_escape(lexer: &mut Lexer<'_>) -> LexResult<()> {
  // We're at '\', consume it
  lexer.skip_expect(1);
  // Expect 'u'
  if lexer.peek(0)? != 'u' {
    return Err(LexNotFound);
  }
  lexer.skip_expect(1);

  // Check for \u{...} or \uXXXX
  if lexer.peek_or_eof(0) == Some('{') {
    // \u{XXXXX} format
    lexer.skip_expect(1);
    let checkpoint = lexer.checkpoint();
    lexer.consume(lexer.while_chars(&DIGIT_HEX));
    let consumed = lexer.next() - checkpoint.next;
    if consumed == 0 {
      return Err(LexNotFound);
    }
    if lexer.peek(0)? != '}' {
      return Err(LexNotFound);
    }
    lexer.skip_expect(1);
  } else {
    // \uXXXX format - expect exactly 4 hex digits
    for _ in 0..4 {
      let c = lexer.peek(0)?;
      if !DIGIT_HEX.has(c) {
        return Err(LexNotFound);
      }
      lexer.skip_expect(1);
    }
  }
  Ok(())
}

fn lex_identifier(
  lexer: &mut Lexer<'_>,
  mode: LexMode,
) -> TT {
  // Consume starter (either a char or a Unicode escape)
  let starter = lexer.peek(0).unwrap();
  if starter == '\\' {
    if lex_unicode_escape(lexer).is_err() {
      return TT::Invalid;
    }
  } else {
    lexer.skip_expect(starter.len_utf8());
  }

  loop {
    // Try to consume regular identifier characters
    lexer.consume(lexer.while_chars(if mode == LexMode::JsxTag {
      &ID_CONTINUE_JSX
    } else {
      &ID_CONTINUE
    }));

    // Check for Unicode escape or UTF-8 multi-byte character
    match lexer.peek_or_eof(0) {
      Some('\\') => {
        if lex_unicode_escape(lexer).is_err() {
          break;
        }
      }
      Some(c) if !c.is_ascii() => {
        lexer.skip_expect(c.len_utf8());
      }
      _ => break,
    }
  }
  TT::Identifier
}

fn lex_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> LexResult<TT> {
  // TODO
  let start_pos = lexer.next();
  let first_char = lexer.peek(0)?;
  lexer.consume(lexer.while_chars(&DIGIT));
  let end_pos = lexer.next();
  if !lexer.consume(lexer.if_char('n')).is_empty() {
    return Ok(TT::LiteralBigInt);
  }
  // Check if this is a legacy octal: starts with 0, has more digits, and all digits are 0-7
  let integer_part = &lexer[Loc(start_pos, end_pos)];
  let is_legacy_octal = first_char == '0'
    && integer_part.len() > 1
    && integer_part.chars().all(|c| matches!(c, '0'..='7'));
  // Consume '.' and fractional part if present (but not for legacy octals)
  if lexer.peek_or_eof(0) == Some('.') && !is_legacy_octal {
    lexer.consume(lexer.if_char('.'));
    lexer.consume(lexer.while_chars(&DIGIT));
  }
  if lexer
    .peek_or_eof(0)
    .filter(|&c| matches!(c, 'e' | 'E'))
    .is_some()
  {
    lexer.skip_expect(1);
    match lexer.peek(0)? {
      '+' | '-' => lexer.skip_expect(1),
      _ => {}
    };
    lexer.consume(lexer.while_chars(&DIGIT));
  }
  Ok(TT::LiteralNumber)
}

fn lex_binary_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> TT {
  lexer.skip_expect(2);
  lexer.consume(lexer.while_chars(&DIGIT_BIN));
  if !lexer.consume(lexer.if_char('n')).is_empty() {
    return TT::LiteralBigInt;
  }
  TT::LiteralNumber
}

fn lex_hex_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> TT {
  lexer.skip_expect(2);
  lexer.consume(lexer.while_chars(&DIGIT_HEX));
  if !lexer.consume(lexer.if_char('n')).is_empty() {
    return TT::LiteralBigInt;
  }
  TT::LiteralNumber
}

fn lex_oct_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> TT {
  lexer.skip_expect(2);
  lexer.consume(lexer.while_chars(&DIGIT_OCT));
  if !lexer.consume(lexer.if_char('n')).is_empty() {
    return TT::LiteralBigInt;
  }
  TT::LiteralNumber
}

fn lex_private_member(
  lexer: &mut Lexer<'_>,
) -> LexResult<TT> {
  // Include the `#` in the token.
  lexer.skip_expect(1);
  let starter = lexer.peek(0)?;
  if !ID_START.has(starter) {
    return Ok(TT::Invalid);
  };
  lexer.skip_expect(starter.len_utf8());
  // TODO This is copied from lex_identifier.
  loop {
    lexer.consume(lexer.while_chars(&ID_CONTINUE));
    // TODO We assume if it's not ASCII it's part of a UTF-8 byte sequence, and that sequence represents a valid JS identifier continue code point.
    if let Some(c) = lexer.peek_or_eof(0).filter(|c| !c.is_ascii()) {
      lexer.skip_expect(c.len_utf8());
    } else {
      break;
    };
  }
  Ok(TT::PrivateMember)
}

// TODO Validate regex.
fn lex_regex(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  // Consume slash.
  lexer.consume(lexer.n(1)?);
  let mut in_charset = false;
  loop {
    // WARNING: Does not consider other line terminators allowed by spec.
    match lexer.consume_next()? {
      '\\' => {
        // Cannot escape line terminator.
        // WARNING: Does not consider other line terminators allowed by spec.
        let escaped_char = lexer.peek(0)?;
        if escaped_char == '\n' {
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
      '\n' => {
        return Ok(TT::Invalid);
      }
      _ => {}
    };
  }
  lexer.consume(lexer.while_chars(&ID_CONTINUE));
  Ok(TT::LiteralRegex)
}

// TODO Validate string.
fn lex_string(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  let quote = lexer.peek(0)?;
  lexer.skip_expect(quote.len_utf8());
  let mut invalid = false;
  loop {
    // Look for backslash, line terminators, or closing quote
    lexer.consume(lexer.while_not_3_chars('\\', '\r', quote));
    // Also check for \n and Unicode line separators
    if let Ok(c) = lexer.peek(0) {
      if c == '\n' || c == '\u{2028}' || c == '\u{2029}' {
        // Bare line terminator without backslash - invalid
        invalid = true;
        lexer.skip_expect(c.len_utf8());
        continue;
      }
    }
    match lexer.peek(0)? {
      '\\' => {
        // Consume the backslash
        lexer.skip_expect(1);
        // Check if next character is a line terminator (line continuation)
        if let Ok(next_char) = lexer.peek(0) {
          match next_char {
            '\r' => {
              // Consume \r, and if followed by \n, consume that too (CRLF)
              lexer.skip_expect(1);
              if lexer.peek(0).ok() == Some('\n') {
                lexer.skip_expect(1);
              }
            }
            '\n' | '\u{2028}' | '\u{2029}' => {
              // Line continuation
              lexer.skip_expect(next_char.len_utf8());
            }
            _ => {
              // Regular escape sequence
              lexer.skip_expect(next_char.len_utf8());
            }
          }
        }
      }
      '\r' => {
        // Bare \r without backslash - invalid
        invalid = true;
        lexer.skip_expect(1);
        // Also consume \n if it follows (CRLF)
        if lexer.peek(0).ok() == Some('\n') {
          lexer.skip_expect(1);
        }
      }
      c if c == quote => {
        lexer.skip_expect(c.len_utf8());
        break;
      }
      _ => unreachable!(),
    };
  }
  if invalid {
    Ok(TT::Invalid)
  } else {
    Ok(TT::LiteralString)
  }
}

/// Ends with `${` or backtick.
pub fn lex_template_string_continue(
  lexer: &mut Lexer<'_>,
) -> LexResult<TT> {
  let mut ended = false;
  loop {
    lexer.consume(lexer.while_not_3_chars('\\', '`', '$'));
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
  };
  let typ = if ended {
    TT::LiteralTemplatePartStringEnd
  } else {
    TT::LiteralTemplatePartString
  };
  Ok(typ)
}

// TODO Validate template.
fn lex_template(lexer: &mut Lexer<'_>) -> LexResult<TT> {
  // Consume backtick.
  lexer.skip_expect(1);
  lex_template_string_continue(lexer)
}

pub fn lex_next(lexer: &mut Lexer<'_>, mode: LexMode) -> Token {
  if mode == LexMode::JsxTextContent {
    return lexer.drive(false, |lexer| {
      // TODO The spec says JSXText cannot contain '>' or '}' either.
      lexer.consume(lexer.while_not_2_chars('{', '<'));
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
        // A single-line comment always ends with a line terminator.
        at_line_start = true;
        preceded_by_line_terminator = true;
        lex_single_comment(lexer, mat);
      }
      _ => unreachable!(),
    };
  };

  // EOF is different from Invalid, so we should emit this specifically instead of letting drive_fallible return an Invalid.
  if lexer.at_end() {
    return Token {
      loc: lexer.eof_range(),
      typ: TT::EOF,
      preceded_by_line_terminator,
    };
  };

  lexer.drive_fallible(preceded_by_line_terminator, |lexer| {
    // Check for non-ASCII identifier start (Unicode identifiers not in ASCII range)
    if let Some(c) = lexer.peek_or_eof(0) {
      if !c.is_ascii() {
        // Non-ASCII character - assume it's an identifier
        return Ok(lex_identifier(lexer, mode));
      }
    }

    SIG.find(lexer).and_then(|(tt, mut mat)| match tt {
      TT::Identifier => Ok(lex_identifier(lexer, mode)),
      TT::LiteralNumber => lex_bigint_or_number(lexer),
      TT::LiteralNumberBin => Ok(lex_binary_bigint_or_number(lexer)),
      TT::LiteralNumberHex => Ok(lex_hex_bigint_or_number(lexer)),
      TT::LiteralNumberOct => Ok(lex_oct_bigint_or_number(lexer)),
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
  })
}
