use crate::error::SyntaxErrorType;
use crate::lex::lex_next;
use crate::lex::LexMode;
use crate::lex::Lexer;
use crate::token::TokenType;
use crate::token::TokenType::*;

fn check(code: &str, expecteds: &[TokenType], expected_err: Option<SyntaxErrorType>) {
  let mut lexer = Lexer::new(code.as_bytes());
  for expected in expecteds {
    match lex_next(&mut lexer, LexMode::Standard) {
      Err(e) => panic!("failed to parse code with error {:?}: {}", e.typ, code),
      Ok(t) => assert_eq!(t.typ, *expected),
    };
  }
  match lex_next(&mut lexer, LexMode::Standard) {
    Err(e) => match expected_err {
      Some(expected) => assert_eq!(e.typ, expected),
      None => panic!("failed to parse code with error {:?}: {}", e.typ, code),
    },
    Ok(t) => match expected_err {
      Some(_) => panic!("code parsed successfully: {}", code),
      None => assert_eq!(EOF, t.typ),
    },
  };
}

#[test]
fn test_lex_keywords() {
  check("class", &[KeywordClass], None);
  check("instanceof", &[KeywordInstanceof], None);
}

#[test]
fn test_lex_identifiers() {
  check("h929", &[Identifier], None);
}

#[test]
fn test_lex_literal_numbers() {
  check("1", &[LiteralNumber], None);
  check("929", &[LiteralNumber], None);
  check(".929", &[LiteralNumber], None);
  check(". 929", &[Dot, LiteralNumber], None);
  check(". 929.2.", &[Dot, LiteralNumber, Dot], None);
  check(".929.2..", &[LiteralNumber, LiteralNumber, Dot, Dot], None);
  check(".929. 2..", &[LiteralNumber, Dot, LiteralNumber, Dot], None);
  check("?.929", &[Question, LiteralNumber], None);
  check("?..929", &[QuestionDot, LiteralNumber], None);
  check("?...929", &[QuestionDot, Dot, LiteralNumber], None);
  check("?...929.", &[QuestionDot, Dot, LiteralNumber, Dot], None);
}

#[test]
fn test_lex_literal_bigints() {
  check("1n", &[LiteralBigInt], None);
  check("929n", &[LiteralBigInt], None);
  check("10000n", &[LiteralBigInt], None);
  check("0x800faceb00cn", &[LiteralBigInt], None);
  check("0b110101010n", &[LiteralBigInt], None);
  check("0o12077n", &[LiteralBigInt], None);
}

#[test]
fn test_lex_literal_strings() {
  check("'hello world'", &[LiteralString], None);
  check(
    "'hello world\n'",
    &[],
    Some(SyntaxErrorType::LineTerminatorInString),
  );
}

#[test]
fn test_lex_import_statement() {
  check(
    "import * as a from \"./a\";",
    &[
      KeywordImport,
      Asterisk,
      KeywordAs,
      Identifier,
      KeywordFrom,
      LiteralString,
      Semicolon,
    ],
    None,
  );
  check(
    "import * as a from './a';",
    &[
      KeywordImport,
      Asterisk,
      KeywordAs,
      Identifier,
      KeywordFrom,
      LiteralString,
      Semicolon,
    ],
    None,
  );
}
