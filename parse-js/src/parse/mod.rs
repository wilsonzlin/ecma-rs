use expr::pat::ParsePatternRules;

use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::lex_next;
use crate::lex::LexMode;
use crate::lex::Lexer;
use crate::loc::Loc;
use crate::token::Token;
use crate::token::TT;

pub mod class_or_object;
pub mod expr;
pub mod func;
pub mod operator;
pub mod stmt;
#[cfg(test)]
mod tests;
pub mod toplevel;
pub mod drive;
pub mod import_export;

// Almost every parse_* function takes these field values as parameters. Instead of having to enumerate them as parameters on every function and ordered unnamed arguments on every call, we simply pass this struct around. Fields are public to allow destructuring, but the value should be immutable; the with_* methods can be used to create an altered copy for passing into other functions, which is useful as most calls simply pass through the values unchanged. This struct should be received as a value, not a reference (i.e. `ctx: ParseCtx` not `ctx: &ParseCtx`) as the latter will require a separate lifetime.
// All fields except `session` can (although not often) change between calls, so we don't simply put them in Parser, as otherwise we'd have to "unwind" (i.e. reset) those values after each call returns.
#[derive(Clone, Copy)]
pub struct ParseCtx {
  pub rules: ParsePatternRules, // For simplicity, this is a copy, not a non-mutable reference, to avoid having a separate lifetime for it. The value is only two booleans, so a reference is probably slower, and it's supposed to be immutable (i.e. changes come from altered copying, not mutating the original single instance), so there shouldn't be any difference between a reference and a copy.
}

impl ParseCtx {
  pub fn with_rules(&self, rules: ParsePatternRules) -> ParseCtx {
    ParseCtx { rules, ..*self }
  }
}

#[derive(Debug)]
#[must_use]
pub struct MaybeToken {
  typ: TT,
  loc: Loc,
  matched: bool,
}

impl MaybeToken {
  pub fn is_match(&self) -> bool {
    self.matched
  }

  pub fn match_loc(&self) -> Option<Loc> {
    if self.matched {
      Some(self.loc)
    } else {
      None
    }
  }

  pub fn error(&self, err: SyntaxErrorType) -> SyntaxError {
    debug_assert!(!self.matched);
    self.loc.error(err, Some(self.typ))
  }

  pub fn map<R, F: FnOnce(Self) -> R>(self, f: F) -> Option<R> {
    if self.matched { Some(f(self)) } else { None }
  }

  pub fn and_then<R, F: FnOnce() -> SyntaxResult<R>>(self, f: F) -> SyntaxResult<Option<R>> {
    Ok(if self.matched { Some(f()?) } else { None })
  }
}

pub struct ParserCheckpoint {
  next_tok_i: usize,
}

/// To get the lexer's `next` after this token was lexed, use `token.loc.1`.
struct BufferedToken {
  token: Token,
  lex_mode: LexMode,
}

pub struct Parser<'a> {
  lexer: Lexer<'a>,
  buf: Vec<BufferedToken>,
  next_tok_i: usize,
}

// We extend this struct with added methods in the various submodules, instead of simply using free functions and passing `&mut Parser` around, for several reasons:
// - Avoid needing to redeclare `<'a>` on every function.
// - More lifetime elision is available for `self` than if it was just another reference parameter.
// - `self` is shorter than `parser` but makes more sense than `p`.
// - Don't need to import each function.
// - Autocomplete is more specific since `self.*` narrows down the options instead of just listing all visible functions (although almost every function currently starts with `parse_` so this is not as significant).
// - For general consistency; if there's no reason why it should be a free function (e.g. more than one ambiguous base type), it should be a method.
// - Makes free functions truly separate independent utility functions.
impl<'a> Parser<'a> {
  pub fn new(lexer: Lexer<'a>) -> Parser<'a> {
    Parser {
      lexer,
      buf: Vec::new(),
      next_tok_i: 0,
    }
  }

  pub fn source_range(&self) -> Loc {
    self.lexer.source_range()
  }

  pub fn bytes(&self, loc: Loc) -> &[u8] {
    &self.lexer[loc]
  }

  pub fn str(&self, loc: Loc) -> &str {
    std::str::from_utf8(self.bytes(loc)).unwrap()
  }

  pub fn string(&self, loc: Loc) -> String {
    self.str(loc).to_string()
  }

  pub fn checkpoint(&self) -> ParserCheckpoint {
    ParserCheckpoint {
      next_tok_i: self.next_tok_i
    }
  }

  pub fn since_checkpoint(&self, checkpoint: &ParserCheckpoint) -> Loc {
    let start = self.buf[checkpoint.next_tok_i].token.loc.1;
    Loc(start, self.lexer.next())
  }

  pub fn restore_checkpoint(&mut self, checkpoint: ParserCheckpoint) {
    self.next_tok_i = checkpoint.next_tok_i;
  }

  fn reset_to(&mut self, n: usize) {
    self.next_tok_i = n;
    self.buf.truncate(n);
    match self.buf.last() {
      Some(t) => self.lexer.set_next(t.token.loc.1),
      None => self.lexer.set_next(0),
    };
  }

  fn forward<K: FnOnce(&Token) -> bool>(
    &mut self,
    mode: LexMode,
    keep: K,
  ) -> (bool, Token) {
    if self.buf.get(self.next_tok_i).is_some_and(|t| t.lex_mode != mode) {
      self.reset_to(self.next_tok_i);
    }
    assert!(self.buf.len() <= self.next_tok_i);
    if self.buf.len() == self.next_tok_i {
      let token = lex_next(&mut self.lexer, mode);
      self.buf.push(BufferedToken { token, lex_mode: mode });
    }
    let t = self.buf[self.next_tok_i].token.clone();
    let k = keep(&t);
    if k {
      self.next_tok_i += 1;
    };
    (k, t)
  }

  pub fn consume_with_mode(&mut self, mode: LexMode) -> Token {
    self.forward(mode, |_| true).1
  }

  pub fn consume(&mut self) -> Token {
    self.consume_with_mode(LexMode::Standard)
  }

  /// Consumes the next token regardless of type, and returns its raw source code as a string.
  pub fn consume_as_string(&mut self) -> String {
    let loc = self.consume().loc;
    self.string(loc)
  }

  pub fn peek_with_mode(&mut self, mode: LexMode) -> Token {
    self.forward(mode, |_| false).1
  }

  pub fn peek(&mut self) -> Token {
    self.peek_with_mode(LexMode::Standard)
  }

  pub fn peek_2_with_mode(&mut self, mode: LexMode) -> (Token, Token) {
    let cp = self.checkpoint();
    let a = self.forward(mode, |_| true);
    let b = self.forward(mode, |_| true);
    self.restore_checkpoint(cp);
    (a.1, b.1)
  }

  pub fn peek_2(&mut self) -> (Token, Token) {
    self.peek_2_with_mode(LexMode::Standard)
  }

  pub fn peek_3(&mut self) -> (Token, Token, Token) {
    let cp = self.checkpoint();
    let a = self.forward(LexMode::Standard, |_| true);
    let b = self.forward(LexMode::Standard, |_| true);
    let c = self.forward(LexMode::Standard, |_| true);
    self.restore_checkpoint(cp);
    (a.1, b.1, c.1)
  }

  pub fn peek_4(&mut self) -> (Token, Token, Token, Token) {
    let cp = self.checkpoint();
    let a = self.forward(LexMode::Standard, |_| true);
    let b = self.forward(LexMode::Standard, |_| true);
    let c = self.forward(LexMode::Standard, |_| true);
    let d = self.forward(LexMode::Standard, |_| true);
    self.restore_checkpoint(cp);
    (a.1, b.1, c.1, d.1)
  }

  pub fn maybe_consume_with_mode(&mut self, typ: TT, mode: LexMode) -> MaybeToken {
    let (matched, t) = self.forward(mode, |t| t.typ == typ);
    MaybeToken {
      typ,
      matched,
      loc: t.loc,
    }
  }

  pub fn consume_if(&mut self, typ: TT) -> MaybeToken {
    self.maybe_consume_with_mode(typ, LexMode::Standard)
  }

  pub fn consume_if_pred<F: FnOnce(&Token) -> bool>(
    &mut self,
    pred: F,
  ) -> MaybeToken {
    let (matched, t) = self.forward(LexMode::Standard, pred);
    MaybeToken {
      typ: t.typ,
      matched,
      loc: t.loc,
    }
  }

  pub fn require_with_mode(&mut self, typ: TT, mode: LexMode) -> SyntaxResult<Token> {
    let t = self.consume_with_mode(mode);
    if t.typ != typ {
      Err(t.error(SyntaxErrorType::RequiredTokenNotFound(typ)))
    } else {
      Ok(t)
    }
  }

  pub fn require_predicate<P: FnOnce(TT) -> bool>(
    &mut self,
    pred: P,
    expected: &'static str,
  ) -> SyntaxResult<Token> {
    let t = self.consume_with_mode(LexMode::Standard);
    if !pred(t.typ) {
      Err(t.error(SyntaxErrorType::ExpectedSyntax(expected)))
    } else {
      Ok(t)
    }
  }

  pub fn require(&mut self, typ: TT) -> SyntaxResult<Token> {
    self.require_with_mode(typ, LexMode::Standard)
  }
}
