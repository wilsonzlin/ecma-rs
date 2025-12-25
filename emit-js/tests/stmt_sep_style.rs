use emit_js::{emit_js_stmt_list, EmitOptions, Emitter, StmtSepStyle};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;

fn parse_program(source: &str) -> Vec<Node<Stmt>> {
  let parsed: Node<TopLevel> = parse_js::parse(source).expect("source should parse");
  parsed.stx.body
}

fn emit_with_style(style: StmtSepStyle) -> String {
  let stmts = parse_program(
    r#"
      const x = 1;
      /re/.test(x)
      x + 1
    "#,
  );
  let mut emitter = Emitter::new(EmitOptions::minified().with_stmt_sep_style(style));
  emit_js_stmt_list(&mut emitter, &stmts).expect("emit should succeed");
  String::from_utf8(emitter.into_bytes()).expect("output is utf-8")
}

#[test]
fn semicolon_style_has_no_newlines() {
  let emitted = emit_with_style(StmtSepStyle::Semicolons);
  assert!(!emitted.contains('\n'));
  parse_js::parse(&emitted).expect("emitted code should parse");
}

#[test]
fn asi_style_inserts_newlines_and_hazard_semicolons() {
  let emitted = emit_with_style(StmtSepStyle::AsiNewlines);
  assert!(emitted.contains('\n'));
  assert!(
    emitted.contains(";/re/.test(x)"),
    "regex hazard should be prefixed by ';'"
  );
  assert!(
    emitted.contains("/re/.test(x)\n"),
    "regex statement should be followed by a newline separator"
  );
  parse_js::parse(&emitted).expect("emitted code should parse");
}
