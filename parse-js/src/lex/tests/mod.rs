use crate::lex::lex_next;
use crate::lex::LexMode;
use crate::lex::Lexer;
use crate::token::TT;
use crate::token::TT::*;

fn check<const N: usize>(code: &str, expecteds: [TT; N]) {
  let mut lexer = Lexer::new(code);
  for expected in expecteds {
    let t = lex_next(&mut lexer, LexMode::Standard);
    assert_eq!(t.typ, expected);
  }
  let t = lex_next(&mut lexer, LexMode::Standard);
  assert_eq!(EOF, t.typ);
}

#[test]
fn test_lex_keywords() {
  check("class", [KeywordClass]);
  check("instanceof", [KeywordInstanceof]);
}

#[test]
fn test_lex_identifiers() {
  check("h929", [Identifier]);
}

#[test]
fn test_lex_literal_numbers() {
  check("1", [LiteralNumber]);
  check("929", [LiteralNumber]);
  check(".929", [LiteralNumber]);
  check(". 929", [Dot, LiteralNumber]);
  check(". 929.2.", [Dot, LiteralNumber, Dot]);
  check(".929.2..", [LiteralNumber, LiteralNumber, Dot, Dot]);
  check(".929. 2..", [LiteralNumber, Dot, LiteralNumber, Dot]);
  check("?.929", [Question, LiteralNumber]);
  check("?..929", [QuestionDot, LiteralNumber]);
  check("?...929", [QuestionDot, Dot, LiteralNumber]);
  check("?...929.", [QuestionDot, Dot, LiteralNumber, Dot]);
}

#[test]
fn test_lex_literal_bigints() {
  check("1n", [LiteralBigInt]);
  check("929n", [LiteralBigInt]);
  check("10000n", [LiteralBigInt]);
  check("0x800faceb00cn", [LiteralBigInt]);
  check("0b110101010n", [LiteralBigInt]);
  check("0o12077n", [LiteralBigInt]);
}

#[test]
fn test_lex_literal_strings() {
  check("'hello world'", [LiteralString]);
  check("'hello world\n'", [Invalid]);
}

#[test]
fn test_lex_import_statement() {
  check(
    "import * as a from \"./a\";",
    [
      KeywordImport,
      Asterisk,
      KeywordAs,
      Identifier,
      KeywordFrom,
      LiteralString,
      Semicolon,
    ],
  );
  check(
    "import * as a from './a';",
    [
      KeywordImport,
      Asterisk,
      KeywordAs,
      Identifier,
      KeywordFrom,
      LiteralString,
      Semicolon,
    ],
  );
}
