use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::lex_next;
use crate::lex::LexMode;
use crate::lex::Lexer;
use crate::loc::Loc;
use crate::token::Token;
use crate::token::TT;
use expr::pat::ParsePatternRules;

pub mod class_or_object;
pub mod drive;
pub mod expr;
pub mod func;
pub mod import_export;
pub mod operator;
pub mod stmt;
#[cfg(test)]
mod tests;
pub mod top_level;
pub mod ts_decl;
pub mod type_expr;

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
    if self.matched {
      Some(f(self))
    } else {
      None
    }
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
// - Don't need to import each function.
// - Autocomplete is more specific since `self.*` narrows down the options instead of just listing all visible functions.
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

  pub fn bytes(&self, loc: Loc) -> &str {
    &self.lexer[loc]
  }

  pub fn str(&self, loc: Loc) -> &str {
    self.bytes(loc)
  }

  pub fn string(&self, loc: Loc) -> String {
    self.str(loc).to_string()
  }

  pub fn checkpoint(&self) -> ParserCheckpoint {
    ParserCheckpoint {
      next_tok_i: self.next_tok_i,
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

  fn forward<K: FnOnce(&Token) -> bool>(&mut self, mode: LexMode, keep: K) -> (bool, Token) {
    if self
      .buf
      .get(self.next_tok_i)
      .is_some_and(|t| t.lex_mode != mode)
    {
      self.reset_to(self.next_tok_i);
    }
    assert!(self.next_tok_i <= self.buf.len());
    if self.buf.len() == self.next_tok_i {
      let token = lex_next(&mut self.lexer, mode);
      self.buf.push(BufferedToken {
        token,
        lex_mode: mode,
      });
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

  pub fn peek_n_with_mode<const N: usize>(&mut self, modes: [LexMode; N]) -> [Token; N] {
    let cp = self.checkpoint();
    let tokens = modes
      .into_iter()
      .map(|m| self.forward(m, |_| true).1)
      .collect::<Vec<_>>();
    let tokens: [Token; N] = tokens.try_into().unwrap();
    self.restore_checkpoint(cp);
    tokens
  }

  pub fn peek_n<const N: usize>(&mut self) -> [Token; N] {
    let cp = self.checkpoint();
    let tokens = (0..N)
      .map(|_| self.forward(LexMode::Standard, |_| true).1)
      .collect::<Vec<_>>();
    let tokens: [Token; N] = tokens.try_into().unwrap();
    self.restore_checkpoint(cp);
    tokens
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

  pub fn consume_if_pred<F: FnOnce(&Token) -> bool>(&mut self, pred: F) -> MaybeToken {
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

  /// Require ChevronRight with support for splitting >> and >>> tokens
  /// This is needed for parsing nested generic types like List<List<T>>
  pub fn require_chevron_right(&mut self) -> SyntaxResult<Token> {
    let t = self.peek();
    match t.typ {
      TT::ChevronRight => {
        // Normal case - consume and return
        Ok(self.consume())
      }
      TT::ChevronRightEquals => {
        // Split >= into > and =
        self.consume();
        let equals_token = Token {
          typ: TT::Equals,
          loc: Loc(t.loc.1 - 1, t.loc.1),
          preceded_by_line_terminator: false,
        };
        self.buf.insert(
          self.next_tok_i,
          BufferedToken {
            token: equals_token,
            lex_mode: LexMode::Standard,
          },
        );
        Ok(Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0, t.loc.0 + 1),
          preceded_by_line_terminator: t.preceded_by_line_terminator,
        })
      }
      TT::ChevronRightChevronRight => {
        // Split >> into > and >
        self.consume(); // Consume the >>
                        // Create a replacement > token to push back
        let split_token = Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0 + 1, t.loc.1), // Second > starts one char later
          preceded_by_line_terminator: false,
        };
        // Insert the second > into the buffer at current position
        self.buf.insert(self.next_tok_i, BufferedToken {
          token: split_token,
          lex_mode: LexMode::Standard,
        });
        // Return a token representing the first >
        Ok(Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0, t.loc.0 + 1),
          preceded_by_line_terminator: t.preceded_by_line_terminator,
        })
      }
      TT::ChevronRightChevronRightEquals => {
        // Split >>= into >, >, =
        self.consume();
        let equals_token = Token {
          typ: TT::Equals,
          loc: Loc(t.loc.1 - 1, t.loc.1),
          preceded_by_line_terminator: false,
        };
        let second = Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0 + 1, t.loc.1 - 1),
          preceded_by_line_terminator: false,
        };
        // Insert in reverse order so the second > is seen before =
        self.buf.insert(
          self.next_tok_i,
          BufferedToken {
            token: equals_token,
            lex_mode: LexMode::Standard,
          },
        );
        self.buf.insert(
          self.next_tok_i,
          BufferedToken {
            token: second,
            lex_mode: LexMode::Standard,
          },
        );
        Ok(Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0, t.loc.0 + 1),
          preceded_by_line_terminator: t.preceded_by_line_terminator,
        })
      }
      TT::ChevronRightChevronRightChevronRight => {
        // Split >>> into > and >>
        self.consume(); // Consume the >>>
                        // Create a >> token to push back
        let split_token = Token {
          typ: TT::ChevronRightChevronRight,
          loc: Loc(t.loc.0 + 1, t.loc.1), // >> starts one char later
          preceded_by_line_terminator: false,
        };
        // Insert the >> into the buffer at current position
        self.buf.insert(self.next_tok_i, BufferedToken {
          token: split_token,
          lex_mode: LexMode::Standard,
        });
        // Return a token representing the first >
        Ok(Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0, t.loc.0 + 1),
          preceded_by_line_terminator: t.preceded_by_line_terminator,
        })
      }
      TT::ChevronRightChevronRightChevronRightEquals => {
        // Split >>>= into >, >>, =
        self.consume();
        let equals_token = Token {
          typ: TT::Equals,
          loc: Loc(t.loc.1 - 1, t.loc.1),
          preceded_by_line_terminator: false,
        };
        let split_token = Token {
          typ: TT::ChevronRightChevronRight,
          loc: Loc(t.loc.0 + 1, t.loc.1 - 1),
          preceded_by_line_terminator: false,
        };
        self.buf.insert(
          self.next_tok_i,
          BufferedToken {
            token: equals_token,
            lex_mode: LexMode::Standard,
          },
        );
        self.buf.insert(
          self.next_tok_i,
          BufferedToken {
            token: split_token,
            lex_mode: LexMode::Standard,
          },
        );
        Ok(Token {
          typ: TT::ChevronRight,
          loc: Loc(t.loc.0, t.loc.0 + 1),
          preceded_by_line_terminator: t.preceded_by_line_terminator,
        })
      }
      _ => Err(t.error(SyntaxErrorType::RequiredTokenNotFound(TT::ChevronRight))),
    }
  }

  /// Require and consume an identifier, returning its string value
  pub fn require_identifier(&mut self) -> SyntaxResult<String> {
    let t = self.consume();
    if t.typ != TT::Identifier {
      return Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier")));
    }
    Ok(self.string(t.loc))
  }

  /// Require an identifier, but allow TypeScript type keywords as identifiers
  /// TypeScript allows type keywords like "any", "string", "number", etc. as identifiers in some contexts
  pub fn require_identifier_or_ts_keyword(&mut self) -> SyntaxResult<String> {
    let t = self.consume();
    // Allow regular identifiers
    if t.typ == TT::Identifier {
      return Ok(self.string(t.loc));
    }
    // Allow TypeScript type keywords as identifiers
    match t.typ {
      TT::KeywordAny
      | TT::KeywordBooleanType
      | TT::KeywordNumberType
      | TT::KeywordStringType
      | TT::KeywordSymbolType
      | TT::KeywordVoid
      | TT::KeywordNever
      | TT::KeywordUndefinedType
      | TT::KeywordUnknown
      | TT::KeywordObjectType
      | TT::KeywordBigIntType => Ok(self.string(t.loc)),
      _ => Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier"))),
    }
  }

  /// Get string value of a template part literal
  pub fn lit_template_part_str_val(&mut self) -> SyntaxResult<String> {
    let t = self.require(TT::LiteralTemplatePartString)?;
    Ok(self.string(t.loc))
  }
}
