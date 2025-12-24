use emit_js::{emit_top_level, emit_ts_stmt};

fn parse_ts(source: &str) -> parse_js::ast::node::Node<parse_js::ast::stx::TopLevel> {
  parse_js::parse(source).expect("source should parse")
}

#[test]
fn emits_ts_only_statements() {
  let source = r#"
    export declare interface Foo {}
    declare namespace A.B.C {}
    declare module "x" { interface Foo {} }
    declare global { interface Foo {} }
    type T = string | number;
    const enum E { A, B }
  "#;

  let parsed = parse_ts(source);

  let expected = [
    "export declare interface Foo {}",
    "declare namespace A.B.C {}",
    "declare module \"x\" { interface Foo {} }",
    "declare global { interface Foo {} }",
    "type T = string | number;",
    "const enum E { A, B }",
  ];

  for (stmt, expected_output) in parsed.stx.body.iter().zip(expected.iter()) {
    let mut out = String::new();
    emit_ts_stmt(&mut out, stmt).expect("emit succeeded");
    assert_eq!(out, *expected_output);

    // Ensure the emitted text parses as valid TypeScript.
    parse_ts(&out);
  }

  let mut all = String::new();
  emit_top_level(&mut all, parsed.stx.as_ref()).expect("full emit");
  assert_eq!(all, expected.join("\n"));
}
