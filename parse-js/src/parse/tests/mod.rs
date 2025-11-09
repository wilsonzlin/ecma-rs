mod expr;
mod stmt;

use crate::{lex::{LexMode, Lexer}, token::TT};
use super::Parser;

#[test]
fn test_parser() {
  let lexer = Lexer::new("let x = /a/ / 1;");
  let mut p = Parser::new(lexer);
  // Initial state.
  let cp = p.checkpoint();
  assert_eq!(p.next_tok_i, 0);

  // Peek the first token.
  let t = p.peek();
  assert_eq!(p.next_tok_i, 0);
  assert_eq!(p.buf.len(), 1);
  assert_eq!(t.typ, TT::KeywordLet);

  // Consume the first token.
  let t = p.consume();
  assert_eq!(p.next_tok_i, 1);
  assert_eq!(p.buf.len(), 1);
  assert_eq!(t.typ, TT::KeywordLet);

  // Consume the second token.
  let t = p.consume();
  assert_eq!(p.next_tok_i, 2);
  assert_eq!(p.buf.len(), 2);
  assert_eq!(t.typ, TT::Identifier);

  // Reset to a past point.
  p.restore_checkpoint(cp);
  assert_eq!(p.next_tok_i, 0);
  assert_eq!(p.buf.len(), 2);

  // Peek using a different mode, which should truncate the buffer.
  let t = p.peek_with_mode(LexMode::SlashIsRegex);
  assert_eq!(p.next_tok_i, 0);
  assert_eq!(p.buf.len(), 1);
  assert_eq!(t.typ, TT::KeywordLet);
}
