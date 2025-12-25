use diagnostics::FileId;
use emit_js::{emit_top_level_diagnostic, EmitOptions};

fn parse(source: &str) -> parse_js::ast::node::Node<parse_js::ast::stx::TopLevel> {
  parse_js::parse(source).expect("source should parse")
}

#[test]
fn reports_unsupported_statement_as_diagnostic() {
  let ast = parse("let x = 1;");
  let diagnostic = emit_top_level_diagnostic(FileId(0), &ast, EmitOptions::default())
    .expect_err("emission should fail for unsupported statements");

  assert!(diagnostic.code.as_str().starts_with("EMIT"));
  assert_eq!(diagnostic.code.as_str(), "EMIT0001");
  assert!(
    diagnostic.primary.range.len() > 0,
    "primary span should be non-empty"
  );
}
