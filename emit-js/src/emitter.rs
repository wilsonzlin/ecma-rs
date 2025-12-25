//! Boundary-aware byte buffer writer used by emitters.
//!
//! The core contract: when callers emit token-like fragments (keywords,
//! identifiers, numbers, punctuation), the [`Emitter`] will automatically
//! insert the minimal whitespace required to prevent the concatenation from
//! being lexed as a different token (e.g. `returnx`, `a++b`, `a--b`). To
//! preserve that boundary tracking, prefer the typed helpers like
//! [`Emitter::write_keyword`], [`Emitter::write_identifier`], and
//! [`Emitter::write_punct`] so the emitter can classify fragments; reserve
//! [`Emitter::write_str`] for a single lexical token or whitespace-only
//! fragments (e.g. indentation, newlines).

use parse_js::loc::Loc;
use std::fmt;

/// Controls how the emitter inserts whitespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EmitMode {
  /// Minified output: only inserts whitespace when necessary to avoid token
  /// ambiguity.
  Minified,
  /// Canonical output: same as minified for now, kept for future expansion
  /// where callers may want stable formatting that still avoids literal
  /// rewrites.
  Canonical,
}

/// Options for configuring output.
#[derive(Clone, Copy, Debug)]
pub struct EmitOptions {
  pub mode: EmitMode,
}

impl Default for EmitOptions {
  fn default() -> Self {
    EmitOptions {
      mode: EmitMode::Minified,
    }
  }
}

#[derive(Debug)]
pub enum EmitErrorKind {
  Fmt(fmt::Error),
  Unsupported(&'static str),
  MissingTypeAnnotation,
}

#[derive(Debug)]
pub struct EmitError {
  pub kind: EmitErrorKind,
  pub loc: Option<Loc>,
}

impl EmitError {
  pub(crate) fn fmt(err: fmt::Error) -> Self {
    Self {
      kind: EmitErrorKind::Fmt(err),
      loc: None,
    }
  }

  pub(crate) fn unsupported(message: &'static str) -> Self {
    Self {
      kind: EmitErrorKind::Unsupported(message),
      loc: None,
    }
  }

  pub(crate) fn missing_type_annotation() -> Self {
    Self {
      kind: EmitErrorKind::MissingTypeAnnotation,
      loc: None,
    }
  }

  pub(crate) fn with_loc(mut self, loc: Loc) -> Self {
    if self.loc.is_none() {
      self.loc = Some(loc);
    }
    self
  }
}

impl From<fmt::Error> for EmitError {
  fn from(value: fmt::Error) -> Self {
    EmitError::fmt(value)
  }
}

pub type EmitResult = Result<(), EmitError>;

pub(crate) fn with_node_context<T>(
  loc: Loc,
  f: impl FnOnce() -> Result<T, EmitError>,
) -> Result<T, EmitError> {
  f().map_err(|err| err.with_loc(loc))
}

#[derive(Debug, Clone)]
pub struct Emitter {
  out: Vec<u8>,
  opts: EmitOptions,
  state: State,
}

#[derive(Debug, Clone, Copy)]
struct State {
  trailing: Boundary,
  html_start: HtmlStart,
}

impl Default for State {
  fn default() -> Self {
    State {
      trailing: Boundary::None,
      html_start: HtmlStart::Start,
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Boundary {
  None,
  Word,
  Number,
  Plus,
  PlusPlus,
  Minus,
  MinusMinus,
  Slash,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Leading {
  None,
  Word,
  Number,
  Plus,
  Minus,
  Slash,
  Star,
  Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
  Word,
  Number,
  Plus,
  PlusPlus,
  Minus,
  MinusMinus,
  Other,
}

#[derive(Debug, Clone, Copy)]
struct FragmentBoundary {
  leading: Leading,
  trailing: Boundary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HtmlStart {
  Start,
  Lt,
  LtBang,
  LtBangDash,
  Dash,
  DashDash,
  Other,
}

impl Emitter {
  pub fn new(opts: EmitOptions) -> Self {
    Emitter {
      out: Vec::new(),
      opts,
      state: State::default(),
    }
  }

  pub fn with_capacity(capacity: usize, opts: EmitOptions) -> Self {
    Emitter {
      out: Vec::with_capacity(capacity),
      opts,
      state: State::default(),
    }
  }

  /// Returns the configured emit mode.
  pub fn mode(&self) -> EmitMode {
    self.opts.mode
  }

  /// Returns the configured options.
  pub fn options(&self) -> EmitOptions {
    self.opts
  }
  /// Returns a read-only view of the buffer.
  pub fn as_bytes(&self) -> &[u8] {
    &self.out
  }

  /// Consumes the emitter, returning the underlying buffer.
  pub fn into_bytes(self) -> Vec<u8> {
    self.out
  }

  /// Clears the buffer and resets token-boundary state.
  pub fn clear(&mut self) {
    self.out.clear();
    self.state = State::default();
  }

  /// Writes a single byte, updating boundary tracking.
  pub fn write_byte(&mut self, byte: u8) {
    let boundary = classify_byte(byte);
    self.insert_boundary(boundary.leading);
    self.insert_html_comment_break(&[byte]);
    self.push_bytes(&[byte]);
    self.state.trailing = boundary.trailing;
  }

  /// Writes an arbitrary string fragment, automatically inserting a space if
  /// it would otherwise merge with the previous token.
  ///
  /// This should only be used for single-token fragments (keywords,
  /// identifiers, numbers, or punctuation) or whitespace-only text. For
  /// multi-token sequences, emit each token via [`Emitter::write_keyword`],
  /// [`Emitter::write_identifier`], or [`Emitter::write_punct`] so the
  /// emitter can correctly track boundaries between them.
  pub fn write_str(&mut self, text: &str) {
    if text.is_empty() {
      return;
    }

    let boundaries = classify_fragment(text.as_bytes());
    self.insert_boundary(boundaries.leading);
    self.insert_html_comment_break(text.as_bytes());
    self.push_bytes(text.as_bytes());
    self.state.trailing = boundaries.trailing;
  }

  pub fn write_keyword(&mut self, keyword: &str) {
    self.write_with_kind(keyword, TokenKind::Word);
  }

  /// Emits an identifier.
  pub fn write_identifier(&mut self, identifier: &str) {
    self.write_with_kind(identifier, TokenKind::Word);
  }

  /// Emits a numeric literal.
  pub fn write_number(&mut self, number: &str) {
    self.write_with_kind(number, TokenKind::Number);
  }

  /// Emits punctuation or operators.
  pub fn write_punct(&mut self, punct: &str) {
    let kind = match punct {
      "+" => TokenKind::Plus,
      "++" => TokenKind::PlusPlus,
      "-" => TokenKind::Minus,
      "--" => TokenKind::MinusMinus,
      _ => TokenKind::Other,
    };
    self.write_with_kind(punct, kind);
  }

  pub fn write_space(&mut self) {
    self.insert_boundary(Leading::None);
    self.push_bytes(&[b' ']);
    self.state.trailing = Boundary::None;
  }

  /// Emits a newline and clears boundary tracking.
  pub fn write_newline(&mut self) {
    self.write_byte(b'\n');
  }

  /// Emits a comma, respecting token boundaries.
  pub fn write_comma(&mut self) {
    self.write_punct(",");
  }

  /// Emits a semicolon, respecting token boundaries.
  pub fn write_semicolon(&mut self) {
    self.write_punct(";");
  }

  /// Writes bytes as-is without attempting to enforce token boundaries.
  /// Resets trailing state to avoid affecting subsequent boundary decisions.
  pub fn write_raw_str(&mut self, text: &str) {
    self.out.extend_from_slice(text.as_bytes());
    self.state.trailing = Boundary::None;
  }

  /// Writes a single byte without boundary handling.
  pub fn write_raw_byte(&mut self, byte: u8) {
    self.out.push(byte);
    self.state.trailing = Boundary::None;
  }

  /// Emits a list of items separated by `separator` and optionally including a
  /// trailing separator.
  pub fn emit_punctuated_list<T>(
    &mut self,
    items: &[T],
    separator: &str,
    trailing_separator: bool,
    mut emit_item: impl FnMut(&mut Self, &T),
  ) {
    for (idx, item) in items.iter().enumerate() {
      emit_item(self, item);
      let is_last = idx + 1 == items.len();
      if !is_last {
        self.write_punct(separator);
      }
    }

    if trailing_separator && !items.is_empty() {
      self.write_punct(separator);
    }
  }

  fn write_with_kind(&mut self, text: &str, kind: TokenKind) {
    if text.is_empty() {
      return;
    }

    let boundaries = classify_fragment_with_kind(text.as_bytes(), kind);
    self.insert_boundary(boundaries.leading);
    self.insert_html_comment_break(text.as_bytes());
    self.push_bytes(text.as_bytes());
    self.state.trailing = boundaries.trailing;
  }

  fn insert_boundary(&mut self, next: Leading) {
    if next == Leading::None {
      return;
    }

    let needs_space = match self.opts.mode {
      EmitMode::Minified => needs_space(self.state.trailing, next),
      EmitMode::Canonical => needs_space(self.state.trailing, next),
    };

    if needs_space {
      self.push_bytes(&[b' ']);
      self.state.trailing = Boundary::None;
    }
  }

  fn insert_html_comment_break(&mut self, bytes: &[u8]) {
    if would_start_html_comment(self.state.html_start, bytes) {
      self.push_bytes(&[b' ']);
      self.state.trailing = Boundary::None;
    }
  }

  fn push_bytes(&mut self, bytes: &[u8]) {
    self.out.extend_from_slice(bytes);
    self.state.html_start = advance_html_start(self.state.html_start, bytes);
  }
}

impl Default for Emitter {
  fn default() -> Self {
    Emitter::new(EmitOptions::default())
  }
}

impl std::fmt::Write for Emitter {
  fn write_str(&mut self, s: &str) -> std::fmt::Result {
    Emitter::write_str(self, s);
    Ok(())
  }

  fn write_char(&mut self, c: char) -> std::fmt::Result {
    let mut buf = [0u8; 4];
    let encoded = c.encode_utf8(&mut buf);
    Emitter::write_str(self, encoded);
    Ok(())
  }
}

fn needs_space(prev: Boundary, next: Leading) -> bool {
  match (prev, next) {
    (Boundary::Word, Leading::Word)
    | (Boundary::Word, Leading::Number)
    | (Boundary::Number, Leading::Word)
    | (Boundary::Number, Leading::Number) => true,
    (Boundary::Plus, Leading::Plus)
    | (Boundary::PlusPlus, Leading::Plus)
    | (Boundary::Minus, Leading::Minus)
    | (Boundary::MinusMinus, Leading::Minus)
    | (Boundary::Slash, Leading::Slash)
    | (Boundary::Slash, Leading::Star) => true,
    _ => false,
  }
}

fn classify_fragment(bytes: &[u8]) -> FragmentBoundary {
  let Some((leading_idx, &leading_char)) = bytes
    .iter()
    .enumerate()
    .find(|(_, b)| !b.is_ascii_whitespace())
  else {
    return FragmentBoundary {
      leading: Leading::None,
      trailing: Boundary::None,
    };
  };

  let leading = if leading_idx == 0 {
    classify_leading_char(leading_char)
  } else {
    Leading::None
  };

  let Some((trailing_idx, _)) = bytes
    .iter()
    .enumerate()
    .rev()
    .find(|(_, b)| !b.is_ascii_whitespace())
  else {
    return FragmentBoundary {
      leading,
      trailing: Boundary::None,
    };
  };

  let trailing = if trailing_idx + 1 == bytes.len() {
    classify_trailing_char(bytes, trailing_idx)
  } else {
    Boundary::None
  };

  FragmentBoundary { leading, trailing }
}

fn classify_fragment_with_kind(bytes: &[u8], kind: TokenKind) -> FragmentBoundary {
  let Some((leading_idx, _)) = bytes
    .iter()
    .enumerate()
    .find(|(_, b)| !b.is_ascii_whitespace())
  else {
    return FragmentBoundary {
      leading: Leading::None,
      trailing: Boundary::None,
    };
  };

  let leading = if leading_idx == 0 {
    match kind {
      TokenKind::Other => match bytes[leading_idx] {
        b'/' => Leading::Slash,
        b'*' => Leading::Star,
        _ => Leading::Other,
      },
      _ => kind.leading(),
    }
  } else {
    Leading::None
  };

  let Some((trailing_idx, _)) = bytes
    .iter()
    .enumerate()
    .rev()
    .find(|(_, b)| !b.is_ascii_whitespace())
  else {
    return FragmentBoundary {
      leading,
      trailing: Boundary::None,
    };
  };

  let trailing = if trailing_idx + 1 == bytes.len() {
    kind.trailing(bytes, trailing_idx)
  } else {
    Boundary::None
  };

  FragmentBoundary { leading, trailing }
}

fn classify_byte(byte: u8) -> FragmentBoundary {
  if byte.is_ascii_whitespace() {
    return FragmentBoundary {
      leading: Leading::None,
      trailing: Boundary::None,
    };
  }

  let leading = classify_leading_char(byte);
  let trailing = classify_trailing_char(&[byte], 0);
  FragmentBoundary { leading, trailing }
}

fn classify_leading_char(ch: u8) -> Leading {
  match ch {
    b'0'..=b'9' => Leading::Number,
    b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'$' => Leading::Word,
    b'+' => Leading::Plus,
    b'-' => Leading::Minus,
    b'/' => Leading::Slash,
    b'*' => Leading::Star,
    _ => Leading::Other,
  }
}

fn classify_trailing_char(bytes: &[u8], idx: usize) -> Boundary {
  let ch = bytes[idx];
  match ch {
    b'0'..=b'9' => Boundary::Number,
    b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'$' => Boundary::Word,
    b'+' => {
      if idx >= 1 && bytes[idx - 1] == b'+' {
        Boundary::PlusPlus
      } else {
        Boundary::Plus
      }
    }
    b'-' => {
      if idx >= 1 && bytes[idx - 1] == b'-' {
        Boundary::MinusMinus
      } else {
        Boundary::Minus
      }
    }
    b'/' => Boundary::Slash,
    _ => Boundary::None,
  }
}

impl TokenKind {
  fn leading(self) -> Leading {
    match self {
      TokenKind::Word => Leading::Word,
      TokenKind::Number => Leading::Number,
      TokenKind::Plus | TokenKind::PlusPlus => Leading::Plus,
      TokenKind::Minus | TokenKind::MinusMinus => Leading::Minus,
      TokenKind::Other => Leading::Other,
    }
  }

  fn trailing(self, bytes: &[u8], trailing_idx: usize) -> Boundary {
    match self {
      TokenKind::PlusPlus => Boundary::PlusPlus,
      TokenKind::MinusMinus => Boundary::MinusMinus,
      TokenKind::Plus => Boundary::Plus,
      TokenKind::Minus => Boundary::Minus,
      TokenKind::Word => Boundary::Word,
      TokenKind::Number => Boundary::Number,
      TokenKind::Other => classify_trailing_char(bytes, trailing_idx),
    }
  }
}

fn advance_html_start(mut state: HtmlStart, bytes: &[u8]) -> HtmlStart {
  for &byte in bytes {
    state = next_html_start(state, byte).0;
  }
  state
}

fn would_start_html_comment(mut state: HtmlStart, bytes: &[u8]) -> bool {
  for &byte in bytes {
    let (next, hazard) = next_html_start(state, byte);
    if hazard {
      return true;
    }
    state = next;
  }
  false
}

fn next_html_start(state: HtmlStart, byte: u8) -> (HtmlStart, bool) {
  if matches!(byte, b'\n' | b'\r') {
    return (HtmlStart::Start, false);
  }

  if byte.is_ascii_whitespace() {
    return match state {
      HtmlStart::Start => (HtmlStart::Start, false),
      HtmlStart::Other => (HtmlStart::Other, false),
      _ => (HtmlStart::Other, false),
    };
  }

  match (state, byte) {
    (HtmlStart::Start, b'<') => (HtmlStart::Lt, false),
    (HtmlStart::Start, b'-') => (HtmlStart::Dash, false),
    (HtmlStart::Start, _) => (HtmlStart::Other, false),
    (HtmlStart::Lt, b'!') => (HtmlStart::LtBang, false),
    (HtmlStart::Lt, _) => (HtmlStart::Other, false),
    (HtmlStart::LtBang, b'-') => (HtmlStart::LtBangDash, false),
    (HtmlStart::LtBang, _) => (HtmlStart::Other, false),
    (HtmlStart::LtBangDash, b'-') => (HtmlStart::Other, true),
    (HtmlStart::LtBangDash, _) => (HtmlStart::Other, false),
    (HtmlStart::Dash, b'-') => (HtmlStart::DashDash, false),
    (HtmlStart::Dash, _) => (HtmlStart::Other, false),
    (HtmlStart::DashDash, b'>') => (HtmlStart::Other, true),
    (HtmlStart::DashDash, _) => (HtmlStart::Other, false),
    (HtmlStart::Other, _) => (HtmlStart::Other, false),
  }
}
