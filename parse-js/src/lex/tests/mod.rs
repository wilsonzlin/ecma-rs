use crate::lex::lex_next;
use crate::lex::LexMode;
use crate::lex::Lexer;
use crate::token::TT;
use crate::token::TT::*;

fn check_with_mode<const N: usize>(code: &str, mode: LexMode, expecteds: [TT; N]) {
  let mut lexer = Lexer::new(code);
  for expected in expecteds {
    let t = lex_next(&mut lexer, mode);
    assert_eq!(t.typ, expected);
  }
  let t = lex_next(&mut lexer, mode);
  assert_eq!(EOF, t.typ);
}

fn check<const N: usize>(code: &str, expecteds: [TT; N]) {
  check_with_mode(code, LexMode::Standard, expecteds);
}

fn check_preceded_by_line_terminator(code: &str, expected: TT, preceded: bool) {
  let mut lexer = Lexer::new(code);
  let t = lex_next(&mut lexer, LexMode::Standard);
  assert_eq!(expected, t.typ);
  assert_eq!(preceded, t.preceded_by_line_terminator);
}

#[test]
fn test_lex_keywords() {
  check("class", [KeywordClass]);
  check("instanceof", [KeywordInstanceof]);
}

#[test]
fn test_keyword_prefix_with_unicode_identifiers() {
  check("classΩ", [Identifier]);
  check("interfaceЖ", [Identifier]);
}

#[test]
fn test_lex_identifiers() {
  check("h929", [Identifier]);
}

#[test]
fn test_unicode_escape_identifiers() {
  check(r"\u0061bc", [Identifier]);
  check(r"a\u{62}c", [Identifier]);
  check(r"\u0063lass", [Identifier]);
}

#[test]
fn test_jsx_identifier_with_hyphen_and_unicode() {
  check_with_mode("Ω-foo", LexMode::JsxTag, [Identifier]);
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
  check("'hello world\r'", [Invalid]);
  check("'hello world\r\n'", [Invalid]);
  check("'hello world\u{2028}'", [Invalid]);
  check("'hello world\u{2029}'", [Invalid]);
  check("'hello\\\nworld'", [LiteralString]);
  check("'hello\\\r\nworld'", [LiteralString]);
  check("'hello\\\u{2028}world'", [LiteralString]);
  check("'hello\\\u{2029}world'", [LiteralString]);
  check("\"hello world\n\"", [Invalid]);
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

#[test]
fn test_single_line_comment_sets_line_terminator_flag_for_unicode_separator() {
  check_preceded_by_line_terminator("// comment\u{2028} token", Identifier, true);
}

#[test]
fn test_multiline_comment_sets_line_terminator_flag_for_unicode_separator() {
  check_preceded_by_line_terminator("/* multi\u{2029}line */ token", Identifier, true);
}

#[test]
fn test_html_close_comment_only_at_line_start() {
  check(
    "a-->b",
    [Identifier, HyphenHyphen, ChevronRight, Identifier],
  );
}

#[test]
fn test_html_close_comment_after_crlf_and_unicode_line_separator() {
  check_preceded_by_line_terminator("\r\n--> comment\r\nfoo", Identifier, true);
  check_preceded_by_line_terminator("\u{2028}--> comment\u{2028}foo", Identifier, true);
}

#[test]
fn test_bom_is_skipped_at_file_start() {
  check_preceded_by_line_terminator("\u{FEFF}foo", Identifier, false);
}
