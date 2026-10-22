use parse_js::ast::stmt::Stmt;
use parse_js::loc::Loc;
use parse_js::parse_with_options;
use parse_js::{Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn parse_ecma(src: &str) -> parse_js::ast::node::Node<parse_js::ast::stx::TopLevel> {
  parse_with_options(src, ecma_script_opts())
    .unwrap_or_else(|err| panic!("expected parse of {src:?} to succeed, got {err:?}"))
}

#[test]
fn labeled_break_consumes_semicolon_no_spurious_empty_stmt() {
  // `break L;` must include `;` in the BreakStmt loc and must not leave an EmptyStmt.
  let src = "L:while(1){break L;}";
  let parsed = parse_ecma(src);
  let Stmt::Label(label) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected labeled statement");
  };
  let Stmt::While(while_stmt) = label.stx.statement.stx.as_ref() else {
    panic!("expected while");
  };
  let Stmt::Block(block) = while_stmt.stx.body.stx.as_ref() else {
    panic!("expected block body");
  };
  assert_eq!(
    block.stx.body.len(),
    1,
    "expected single statement in block"
  );
  let break_stmt = &block.stx.body[0];
  assert!(
    matches!(break_stmt.stx.as_ref(), Stmt::Break(_)),
    "expected BreakStmt, got {:?}",
    break_stmt.stx.as_ref()
  );
  assert!(
    !matches!(break_stmt.stx.as_ref(), Stmt::Empty(_)),
    "semicolon must not become EmptyStmt"
  );
  // Span includes the terminating semicolon: `break L;`
  let break_text = &src[break_stmt.loc.0..break_stmt.loc.1];
  assert_eq!(break_text, "break L;");
  assert_eq!(
    break_stmt.loc,
    Loc(src.find("break L;").unwrap(), src.len() - 1)
  );
}

#[test]
fn labeled_continue_consumes_semicolon_no_spurious_empty_stmt() {
  let src = "L:while(1){continue L;}";
  let parsed = parse_ecma(src);
  let Stmt::Label(label) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected labeled statement");
  };
  let Stmt::While(while_stmt) = label.stx.statement.stx.as_ref() else {
    panic!("expected while");
  };
  let Stmt::Block(block) = while_stmt.stx.body.stx.as_ref() else {
    panic!("expected block body");
  };
  assert_eq!(block.stx.body.len(), 1);
  let cont = &block.stx.body[0];
  assert!(matches!(cont.stx.as_ref(), Stmt::Continue(_)));
  assert_eq!(&src[cont.loc.0..cont.loc.1], "continue L;");
}

#[test]
fn unlabeled_break_asi_at_eof() {
  // EOF is an ASI boundary for the restricted `break` production (ECMA-262 §12.10).
  let parsed = parse_ecma("while(1)break");
  let Stmt::While(while_stmt) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected while");
  };
  assert!(matches!(while_stmt.stx.body.stx.as_ref(), Stmt::Break(_)));
  assert_eq!(
    &"while(1)break"[while_stmt.stx.body.loc.0..while_stmt.stx.body.loc.1],
    "break"
  );
}

#[test]
fn unlabeled_continue_asi_at_eof() {
  let parsed = parse_ecma("while(1)continue");
  let Stmt::While(while_stmt) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected while");
  };
  assert!(matches!(
    while_stmt.stx.body.stx.as_ref(),
    Stmt::Continue(_)
  ));
}

#[test]
fn do_continue_with_semicolon() {
  let src = "do continue; while(0)";
  let parsed = parse_ecma(src);
  let Stmt::DoWhile(do_while) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected do-while");
  };
  let cont = &do_while.stx.body;
  assert!(matches!(cont.stx.as_ref(), Stmt::Continue(_)));
  assert_eq!(&src[cont.loc.0..cont.loc.1], "continue;");
}

#[test]
fn return_asi_at_eof_inside_unclosed_function() {
  // `return` treats EOF as ASI for its optional expression (same gap as break).
  // The program is still incomplete (missing `}`), so parse fails — but on the
  // missing brace, not on a spurious "expression operand" after `return`.
  let err = parse_with_options("function f(){return", ecma_script_opts()).unwrap_err();
  assert!(
    !matches!(
      err.typ,
      parse_js::error::SyntaxErrorType::ExpectedSyntax("expression operand")
    ),
    "return at EOF must ASI before failing on unclosed function body, got {:?}",
    err.typ
  );
  assert!(matches!(
    err.typ,
    parse_js::error::SyntaxErrorType::RequiredTokenNotFound(parse_js::token::TT::BraceClose)
  ));
}
