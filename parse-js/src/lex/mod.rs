use crate::char::CharFilter;
use crate::char::DIGIT;
use crate::char::DIGIT_BIN;
use crate::char::DIGIT_HEX;
use crate::char::DIGIT_OCT;
use crate::char::ID_CONTINUE;
use crate::char::ID_CONTINUE_CHARSTR;
use crate::char::ID_CONTINUE_JSX;
use crate::char::ID_START;
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
  pub fn new<D: AsRef<[u8]>>(anchored: bool, patterns: Vec<(TT, D)>) -> Self {
    let (tts, syns): (Vec<_>, Vec<_>) = patterns.into_iter().unzip();
    let matcher = AhoCorasickBuilder::new()
      .start_kind(if anchored {
        StartKind::Anchored
      } else {
        StartKind::Unanchored
      })
      .kind(Some(AhoCorasickKind::DFA))
      .match_kind(MatchKind::LeftmostLongest)
      .build(syns)
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

struct LexNotFound;

type LexResult<T> = Result<T, LexNotFound>;

pub struct Lexer<'a> {
  source: &'a [u8],
  next: usize,
}

impl<'a> Lexer<'a> {
  pub fn new(code: &'a [u8]) -> Lexer<'a> {
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

  fn peek(&self, n: usize) -> LexResult<u8> {
    self
      .peek_or_eof(n)
      .ok_or_else(|| LexNotFound)
  }

  fn peek_or_eof(&self, n: usize) -> Option<u8> {
    self.source.get(self.next + n).copied()
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

  fn if_char(&self, c: u8) -> Match {
    Match(
      (!self.at_end() && self.source[self.next] == c) as usize,
    )
  }

  fn through_char_or_end(&self, c: u8) -> Match {
    memchr(c, &self.source[self.next..])
      .map(|pos| Match(pos + 1))
      .unwrap_or_else(|| Match(self.remaining()))
  }

  fn through_char(&self, c: u8) -> LexResult<Match> {
    memchr(c, &self.source[self.next..])
      .map(|pos| Match(pos + 1))
      .ok_or_else(|| LexNotFound)
  }

  fn while_not_char(&self, a: u8) -> Match {
    Match(
      memchr(a, &self.source[self.next..]).unwrap_or(self.remaining()),
    )
  }

  fn while_not_2_chars(&self, a: u8, b: u8) -> Match {
    Match(
      memchr2(a, b, &self.source[self.next..]).unwrap_or(self.remaining()),
    )
  }

  fn while_not_3_chars(&self, a: u8, b: u8, c: u8) -> Match {
    Match(
      memchr3(a, b, c, &self.source[self.next..]).unwrap_or(self.remaining()),
    )
  }

  fn while_chars(&self, chars: &CharFilter) -> Match {
    let mut len = 0;
    while len < self.remaining() && chars.has(self.source[self.next + len]) {
      len += 1;
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

  fn consume_next(&mut self) -> LexResult<u8> {
    let c = self.peek(0)?;
    self.next += 1;
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
  type Output = [u8];

  fn index(&self, index: Loc) -> &Self::Output {
    &self.source[index.0..index.1]
  }
}

impl<'a> Index<Match> for Lexer<'a> {
  type Output = [u8];

  fn index(&self, m: Match) -> &Self::Output {
    &self.source[self.next - m.len()..self.next]
  }
}

#[rustfmt::skip]
pub static OPERATORS_MAPPING: Lazy<HashMap<TT, &'static [u8]>> = Lazy::new(|| {
  let mut map = HashMap::<TT, &'static [u8]>::new();
  map.insert(TT::Ampersand, b"&");
  map.insert(TT::AmpersandAmpersand, b"&&");
  map.insert(TT::AmpersandAmpersandEquals, b"&&=");
  map.insert(TT::AmpersandEquals, b"&=");
  map.insert(TT::Asterisk, b"*");
  map.insert(TT::AsteriskAsterisk, b"**");
  map.insert(TT::AsteriskAsteriskEquals, b"**=");
  map.insert(TT::AsteriskEquals, b"*=");
  map.insert(TT::Bar, b"|");
  map.insert(TT::BarBar, b"||");
  map.insert(TT::BarBarEquals, b"||=");
  map.insert(TT::BarEquals, b"|=");
  map.insert(TT::BraceClose, b"}");
  map.insert(TT::BraceOpen, b"{");
  map.insert(TT::BracketClose, b"]");
  map.insert(TT::BracketOpen, b"[");
  map.insert(TT::Caret, b"^");
  map.insert(TT::CaretEquals, b"^=");
  map.insert(TT::ChevronLeft, b"<");
  map.insert(TT::ChevronLeftChevronLeft, b"<<");
  map.insert(TT::ChevronLeftChevronLeftEquals, b"<<=");
  map.insert(TT::ChevronLeftEquals, b"<=");
  map.insert(TT::ChevronRight, b">");
  map.insert(TT::ChevronRightChevronRight, b">>");
  map.insert(TT::ChevronRightChevronRightChevronRight, b">>>");
  map.insert(TT::ChevronRightChevronRightChevronRightEquals, b">>>=");
  map.insert(TT::ChevronRightChevronRightEquals, b">>=");
  map.insert(TT::ChevronRightEquals, b">=");
  map.insert(TT::Colon, b":");
  map.insert(TT::Comma, b",");
  map.insert(TT::Dot, b".");
  map.insert(TT::DotDotDot, b"...");
  map.insert(TT::Equals, b"=");
  map.insert(TT::EqualsChevronRight, b"=>");
  map.insert(TT::EqualsEquals, b"==");
  map.insert(TT::EqualsEqualsEquals, b"===");
  map.insert(TT::Exclamation, b"!");
  map.insert(TT::ExclamationEquals, b"!=");
  map.insert(TT::ExclamationEqualsEquals, b"!==");
  map.insert(TT::Hyphen, b"-");
  map.insert(TT::HyphenEquals, b"-=");
  map.insert(TT::HyphenHyphen, b"--");
  map.insert(TT::ParenthesisClose, b")");
  map.insert(TT::ParenthesisOpen, b"(");
  map.insert(TT::Percent, b"%");
  map.insert(TT::PercentEquals, b"%=");
  map.insert(TT::Plus, b"+");
  map.insert(TT::PlusEquals, b"+=");
  map.insert(TT::PlusPlus, b"++");
  map.insert(TT::PrivateMember, b"#");
  map.insert(TT::Question, b"?");
  map.insert(TT::QuestionDot, b"?.");
  map.insert(TT::QuestionDotBracketOpen, b"?.[");
  map.insert(TT::QuestionDotParenthesisOpen, b"?.(");
  map.insert(TT::QuestionQuestion, b"??");
  map.insert(TT::QuestionQuestionEquals, b"??=");
  map.insert(TT::Semicolon, b";");
  map.insert(TT::Slash, b"/");
  map.insert(TT::SlashEquals, b"/=");
  map.insert(TT::Tilde, b"~");
  map
});

pub static KEYWORDS_MAPPING: Lazy<HashMap<TT, &'static [u8]>> = Lazy::new(|| {
  let mut map = HashMap::<TT, &'static [u8]>::new();
  map.insert(TT::KeywordAs, b"as");
  map.insert(TT::KeywordAsync, b"async");
  map.insert(TT::KeywordAwait, b"await");
  map.insert(TT::KeywordBreak, b"break");
  map.insert(TT::KeywordCase, b"case");
  map.insert(TT::KeywordCatch, b"catch");
  map.insert(TT::KeywordClass, b"class");
  map.insert(TT::KeywordConst, b"const");
  map.insert(TT::KeywordConstructor, b"constructor");
  map.insert(TT::KeywordContinue, b"continue");
  map.insert(TT::KeywordDebugger, b"debugger");
  map.insert(TT::KeywordDefault, b"default");
  map.insert(TT::KeywordDelete, b"delete");
  map.insert(TT::KeywordDo, b"do");
  map.insert(TT::KeywordElse, b"else");
  map.insert(TT::KeywordEnum, b"enum");
  map.insert(TT::KeywordExport, b"export");
  map.insert(TT::KeywordExtends, b"extends");
  map.insert(TT::KeywordFinally, b"finally");
  map.insert(TT::KeywordFor, b"for");
  map.insert(TT::KeywordFrom, b"from");
  map.insert(TT::KeywordFunction, b"function");
  map.insert(TT::KeywordGet, b"get");
  map.insert(TT::KeywordIf, b"if");
  map.insert(TT::KeywordImport, b"import");
  map.insert(TT::KeywordIn, b"in");
  map.insert(TT::KeywordInstanceof, b"instanceof");
  map.insert(TT::KeywordLet, b"let");
  map.insert(TT::KeywordNew, b"new");
  map.insert(TT::KeywordOf, b"of");
  map.insert(TT::KeywordReturn, b"return");
  map.insert(TT::KeywordSet, b"set");
  map.insert(TT::KeywordStatic, b"static");
  map.insert(TT::KeywordSuper, b"super");
  map.insert(TT::KeywordSwitch, b"switch");
  map.insert(TT::KeywordThis, b"this");
  map.insert(TT::KeywordThrow, b"throw");
  map.insert(TT::KeywordTry, b"try");
  map.insert(TT::KeywordTypeof, b"typeof");
  map.insert(TT::KeywordVar, b"var");
  map.insert(TT::KeywordVoid, b"void");
  map.insert(TT::KeywordWhile, b"while");
  map.insert(TT::KeywordWith, b"with");
  map.insert(TT::KeywordYield, b"yield");
  map.insert(TT::LiteralFalse, b"false");
  map.insert(TT::LiteralNull, b"null");
  map.insert(TT::LiteralTrue, b"true");
  map
});

pub static KEYWORD_STRS: Lazy<HashMap<&'static [u8], usize>> = Lazy::new(|| {
  HashMap::<&'static [u8], usize>::from_iter(
    KEYWORDS_MAPPING.values().enumerate().map(|(i, v)| (*v, i)),
  )
});

#[rustfmt::skip]
static SIG: Lazy<PatternMatcher> = Lazy::new(|| {
  let mut patterns: Vec<(TT, Vec<u8>)> = Vec::new();
  for (&k, &v) in OPERATORS_MAPPING.iter() {
    patterns.push((k, v.into()));
  }
  for (&k, &v) in KEYWORDS_MAPPING.iter() {
    patterns.push((k, v.into()));
    // Avoid accidentally matching an identifier starting with a keyword as a keyword.
    for &c in ID_CONTINUE_CHARSTR {
      let mut v = v.to_vec();
      v.push(c);
      if !KEYWORD_STRS.contains_key(v.as_slice()) {
        patterns.push((TT::Identifier, v));
      }
    }
  }
  // TODO We assume that if it's a UTF-8 non-ASCII sequence it's an identifier, but JS only allows a few Unicode property types as identifiers.
  for c in 0..255 {
    if ID_START.has(c) || c >> 5 == 0b110 || c >> 4 == 0b1110 || c >> 3 == 0b11110 {
      patterns.push((TT::Identifier, vec![c]));
    }
  }
  for c in b"0123456789".chunks(1) {
    patterns.push((TT::LiteralNumber, c.into()));
  }
  patterns.push((TT::LiteralNumberBin, b"0b".into()));
  patterns.push((TT::LiteralNumberBin, b"0B".into()));
  patterns.push((TT::LiteralNumberHex, b"0x".into()));
  patterns.push((TT::LiteralNumberHex, b"0X".into()));
  patterns.push((TT::LiteralNumberOct, b"0o".into()));
  patterns.push((TT::LiteralNumberOct, b"0O".into()));
  // Prevent `.` immediately followed by a digit from being recognised as the `.` operator.
  for c in b".0.1.2.3.4.5.6.7.8.9".chunks(2) {
    patterns.push((TT::LiteralNumber, c.into()));
  }
  // Prevent `?` immediately followed by a decimal number from being recognised as the `?.` operator.
  for c in b"?.0?.1?.2?.3?.4?.5?.6?.7?.8?.9".chunks(3) {
    patterns.push((TT::Question, c.into()));
  }
  patterns.push((TT::ChevronLeftSlash, b"</".into()));
  patterns.push((TT::LiteralString, b"\"".into()));
  patterns.push((TT::LiteralString, b"'".into()));
  patterns.push((TT::LiteralTemplatePartString, b"`".into()));

  PatternMatcher::new(true, patterns)
});

static ML_COMMENT: Lazy<PatternMatcher> = Lazy::new(|| {
  PatternMatcher::new::<&[u8]>(false, vec![
    (TT::CommentMultilineEnd, b"*/"),
    // WARNING: Does not consider Unicode whitespace allowed by spec.
    (TT::LineTerminator, b"\r"),
    (TT::LineTerminator, b"\n"),
  ])
});

static INSIG: Lazy<PatternMatcher> = Lazy::new(|| {
  // WARNING: Does not consider Unicode whitespace allowed by spec.
  PatternMatcher::new::<&[u8]>(
    true,
    vec![
      (TT::LineTerminator, b"\r"),
      (TT::LineTerminator, b"\n"),
      (TT::Whitespace, b"\x09"),
      (TT::Whitespace, b"\x0b"),
      (TT::Whitespace, b"\x0c"),
      (TT::Whitespace, b"\x20"),
      (TT::CommentMultiline, b"/*"),
      (TT::CommentSingle, b"//"),
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
      TT::CommentMultiline | TT::EOF => {
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

fn lex_single_comment(lexer: &mut Lexer<'_>) {
  // Consume `//`.
  lexer.skip_expect(2);
  // WARNING: Does not consider other line terminators allowed by spec.
  lexer.consume(lexer.through_char_or_end(b'\n'));
}

fn lex_identifier(
  lexer: &mut Lexer<'_>,
  mode: LexMode,
) -> TT {
  // Consume starter.
  lexer.skip_expect(1);
  loop {
    lexer.consume(lexer.while_chars(if mode == LexMode::JsxTag {
      &ID_CONTINUE_JSX
    } else {
      &ID_CONTINUE
    }));
    // TODO We assume if it's not ASCII it's part of a UTF-8 byte sequence, and that sequence represents a valid JS identifier continue code point.
    if lexer.peek_or_eof(0).filter(|c| !c.is_ascii()).is_none() {
      break;
    };
    lexer.skip_expect(1);
  }
  TT::Identifier
}

fn lex_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> LexResult<TT> {
  // TODO
  lexer.consume(lexer.while_chars(&DIGIT));
  if !lexer.consume(lexer.if_char(b'n')).is_empty() {
    return Ok(TT::LiteralBigInt);
  }
  lexer.consume(lexer.if_char(b'.'));
  lexer.consume(lexer.while_chars(&DIGIT));
  if lexer
    .peek_or_eof(0)
    .filter(|&c| matches!(c,  b'e' | b'E'))
    .is_some()
  {
    lexer.skip_expect(1);
    match lexer.peek(0)? {
      b'+' | b'-' => lexer.skip_expect(1),
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
  if !lexer.consume(lexer.if_char(b'n')).is_empty() {
    return TT::LiteralBigInt;
  }
  TT::LiteralNumber
}

fn lex_hex_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> TT {
  lexer.skip_expect(2);
  lexer.consume(lexer.while_chars(&DIGIT_HEX));
  if !lexer.consume(lexer.if_char(b'n')).is_empty() {
    return TT::LiteralBigInt;
  }
  TT::LiteralNumber
}

fn lex_oct_bigint_or_number(
  lexer: &mut Lexer<'_>,
) -> TT {
  lexer.skip_expect(2);
  lexer.consume(lexer.while_chars(&DIGIT_OCT));
  if !lexer.consume(lexer.if_char(b'n')).is_empty() {
    return TT::LiteralBigInt;
  }
  TT::LiteralNumber
}

fn lex_private_member(
  lexer: &mut Lexer<'_>,
) -> LexResult<TT> {
  // Include the `#` in the token.
  lexer.skip_expect(1);
  if !ID_START.has(lexer.peek(0)?) {
    return Ok(TT::Invalid);
  };
  lexer.skip_expect(1);
  // TODO This is copied from lex_identifier.
  loop {
    lexer.consume(lexer.while_chars(&ID_CONTINUE));
    // TODO We assume if it's not ASCII it's part of a UTF-8 byte sequence, and that sequence represents a valid JS identifier continue code point.
    if lexer.peek_or_eof(0).filter(|c| !c.is_ascii()).is_none() {
      break;
    };
    lexer.skip_expect(1);
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
      b'\\' => {
        // Cannot escape line terminator.
        // WARNING: Does not consider other line terminators allowed by spec.
        if lexer.peek(1)? == b'\n' {
          return Ok(TT::Invalid);
        };
        lexer.skip_expect(1);
      }
      b'/' if !in_charset => {
        break;
      }
      b'[' => {
        in_charset = true;
      }
      b']' if in_charset => {
        in_charset = false;
      }
      b'\n' => {
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
  lexer.skip_expect(1);
  loop {
    // TODO Does not consider other line terminators allowed by spec.
    lexer.consume(lexer.while_not_3_chars(b'\\', b'\n', quote));
    match lexer.peek(0)? {
      b'\\' => {
        lexer.consume(lexer.n(2)?);
      }
      b'\n' => {
        return Ok(TT::Invalid);
      }
      c if c == quote => {
        lexer.skip_expect(1);
        break;
      }
      _ => unreachable!(),
    };
  }
  Ok(TT::LiteralString)
}

/// Ends with `${` or backtick.
pub fn lex_template_string_continue(
  lexer: &mut Lexer<'_>,
) -> LexResult<TT> {
  let mut ended = false;
  loop {
    lexer.consume(lexer.while_not_3_chars(b'\\', b'`', b'$'));
    match lexer.peek(0)? {
      b'\\' => {
        lexer.consume(lexer.n(2)?);
      }
      b'`' => {
        ended = true;
        lexer.skip_expect(1);
        break;
      }
      b'$' => {
        if lexer.peek(1)? == b'{' {
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
      lexer.consume(lexer.while_not_2_chars(b'{', b'<'));
      TT::JsxTextContent
    });
  };

  if mode == LexMode::TemplateStrContinue {
    return lexer.drive_fallible(false, |lexer| lex_template_string_continue(lexer));
  };

  // Skip whitespace and comments before the next significant token.
  let mut preceded_by_line_terminator = false;
  while let Ok((tt, mat)) = INSIG.find(&lexer) {
    match tt {
      TT::LineTerminator => {
        lexer.consume(mat);
        preceded_by_line_terminator = true;
      }
      TT::Whitespace => {
        lexer.consume(mat);
      }
      TT::CommentMultiline => {
        let comment_has_line_terminator = lex_multiline_comment(lexer);
        preceded_by_line_terminator |= comment_has_line_terminator;
      }
      TT::CommentSingle => {
        // A single-line comment always ends with a line terminator.
        preceded_by_line_terminator = true;
        lex_single_comment(lexer);
      }
      _ => unreachable!(),
    };
  };

  lexer.drive_fallible(preceded_by_line_terminator, |lexer| {
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
