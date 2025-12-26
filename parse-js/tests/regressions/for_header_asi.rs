use parse_js::ast::stmt::{ForTripleStmtInit, Stmt};
use parse_js::parse_with_options;
use parse_js::{Dialect, ParseOptions, SourceType};

fn script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

#[test]
fn for_in_header_handles_line_terminators() {
  assert!(parse_with_options("for (foo\n in bar) {}", script_opts()).is_ok());
}

#[test]
fn for_of_header_handles_line_terminators() {
  assert!(parse_with_options("for (foo\n of bar) {}", script_opts()).is_ok());
}

#[test]
fn for_in_header_with_initializer_recovers_and_classifies() {
  let parsed = parse_with_options("for (var i = foo in bar) {}", script_opts()).unwrap();
  match parsed.stx.body.first().unwrap().stx.as_ref() {
    Stmt::ForIn(_) => {}
    other => panic!("expected for-in statement, got {:?}", other),
  }
}

#[test]
fn for_triple_header_allows_parenthesised_in_operator() {
  let parsed = parse_with_options("for (var i = (foo in bar); i; ) {}", script_opts()).unwrap();
  match parsed.stx.body.first().unwrap().stx.as_ref() {
    Stmt::ForTriple(triple) => match &triple.stx.init {
      ForTripleStmtInit::Decl(_) => {}
      other => panic!("unexpected for(;;) init: {:?}", other),
    },
    other => panic!("expected for(;;) statement, got {:?}", other),
  }
}
