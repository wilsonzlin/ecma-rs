use crate::lex::lex_next;
use crate::lex::LexMode;
use crate::lex::Lexer;
use crate::token::TT;
use crate::token::TT::*;
use crate::Dialect;

fn check<const N: usize>(code: &str, expecteds: [TT; N], dialect: Dialect) {
  let mut lexer = Lexer::new(code);
  for expected in expecteds {
    let t = lex_next(&mut lexer, LexMode::Standard, dialect);
    assert_eq!(t.typ, expected);
  }
  let t = lex_next(&mut lexer, LexMode::Standard, dialect);
  assert_eq!(EOF, t.typ);
}

#[test]
fn test_lex_keywords() {
  check("class", [KeywordClass], Dialect::Tsx);
  check("instanceof", [KeywordInstanceof], Dialect::Tsx);
}

#[test]
fn test_lex_identifiers() {
  check("h929", [Identifier], Dialect::Tsx);
}

#[test]
fn test_lex_literal_numbers() {
  check("1", [LiteralNumber], Dialect::Tsx);
  check("929", [LiteralNumber], Dialect::Tsx);
  check(".929", [LiteralNumber], Dialect::Tsx);
  check(". 929", [Dot, LiteralNumber], Dialect::Tsx);
  check(". 929.2.", [Dot, LiteralNumber, Dot], Dialect::Tsx);
  check(".929.2..", [LiteralNumber, LiteralNumber, Dot, Dot], Dialect::Tsx);
  check(".929. 2..", [LiteralNumber, Dot, LiteralNumber, Dot], Dialect::Tsx);
  check("?.929", [Question, LiteralNumber], Dialect::Tsx);
  check("?..929", [QuestionDot, LiteralNumber], Dialect::Tsx);
  check("?...929", [QuestionDot, Dot, LiteralNumber], Dialect::Tsx);
  check("?...929.", [QuestionDot, Dot, LiteralNumber, Dot], Dialect::Tsx);
}

#[test]
fn test_lex_literal_bigints() {
  check("1n", [LiteralBigInt], Dialect::Tsx);
  check("929n", [LiteralBigInt], Dialect::Tsx);
  check("10000n", [LiteralBigInt], Dialect::Tsx);
  check("0x800faceb00cn", [LiteralBigInt], Dialect::Tsx);
  check("0b110101010n", [LiteralBigInt], Dialect::Tsx);
  check("0o12077n", [LiteralBigInt], Dialect::Tsx);
}

#[test]
fn test_lex_literal_strings() {
  check("'hello world'", [LiteralString], Dialect::Tsx);
  check("'hello world\n'", [Invalid], Dialect::Tsx);
  check("'hello world\r'", [Invalid], Dialect::Tsx);
  check("'hello world\r\n'", [Invalid], Dialect::Tsx);
  check("'hello world\u{2028}'", [Invalid], Dialect::Tsx);
  check("'hello world\u{2029}'", [Invalid], Dialect::Tsx);
  check("'hello\\\nworld'", [LiteralString], Dialect::Tsx);
  check("'hello\\\r\nworld'", [LiteralString], Dialect::Tsx);
  check("'hello\\\u{2028}world'", [LiteralString], Dialect::Tsx);
  check("'hello\\\u{2029}world'", [LiteralString], Dialect::Tsx);
  check("\"hello world\n\"", [Invalid], Dialect::Tsx);
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
    Dialect::Tsx,
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
    Dialect::Tsx,
  );
}

#[test]
fn ts_keywords_follow_dialect() {
  check("interface", [Identifier], Dialect::Js);
  check("type", [Identifier], Dialect::Jsx);
  check("interface", [KeywordInterface], Dialect::Ts);
}
