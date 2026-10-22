//! `let` + LineTerminator in Statement (not StatementListItem) position.
//!
//! Regression for PS0018 over-rejecting test262:
//! - `language/statements/{if,while,for,labeled}/let-{block,identifier}-with-newline.js`
//!
//! Rule (ECMA-262):
//! - LexicalDeclaration: `LetOrConst BindingList` — **no** `[no LineTerminator here]`,
//!   so at StatementListItem `let\nx` / `let\n[a]=…` are declarations.
//! - ExpressionStatement lookahead forbids only `let [` (§14.11), not `let {` or
//!   `let BindingIdentifier`. In Statement position (if/while/for/label body),
//!   Declaration is illegal; with a LineTerminator before `{` or BindingIdentifier,
//!   ASI ends ExpressionStatement `let;` and the following tokens are a separate
//!   statement — so `if (c) let\nx;` / `if (c) let\n{}` are legal in sloppy code.
//! - `let [` remains ExpressionStatement-forbidden across LT, so `if (c) let\n[a]=…`
//!   is still PS0018.

use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn assert_accept(src: &str) {
  parse_with_options(src, ecma_script()).unwrap_or_else(|err| {
    panic!("expected accept {src:?}, got {err:?}");
  });
}

fn assert_reject_code(src: &str, code: &str) {
  let err = parse_with_options(src, ecma_script()).expect_err(&format!("expected reject: {src:?}"));
  assert_eq!(err.typ.code(), code, "src={src:?} err={err:?}");
}

#[test]
fn let_newline_asi_in_single_statement_position() {
  // Corpus shapes (noStrict script).
  assert_accept("for (; false; ) let\n{}");
  assert_accept("for (; false; ) let\nx = 1;");
  assert_accept("if (false) let\n{}");
  assert_accept("if (false) let\nx = 1;");
  assert_accept("if (false) {\n    L: let\n    {}\n}");
  assert_accept("if (false) {\n    L: let\n    x = 1;\n}");
  assert_accept("while (false) let\n{}");
  assert_accept("while (false) let\nx = 1;");

  // Same-line lexical heads remain illegal in Statement position.
  assert_reject_code("if (false) let x = 1;", "PS0018");
  assert_reject_code("if (false) let {}", "PS0018");
  assert_reject_code("if (false) let[a] = [];", "PS0018");
  // `let [` lookahead restriction ignores LineTerminator.
  assert_reject_code("if (false) let\n[a] = [];", "PS0018");

  // StatementListItem keeps declaration-across-LT.
  assert_accept("let\nx = 1;");
  assert_accept("let\n[a] = [];");
  assert_accept("let\n{a} = {};");
}
