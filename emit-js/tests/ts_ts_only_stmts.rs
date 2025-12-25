use emit_js::{emit_top_level, emit_ts_stmt, EmitMode, EmitOptions, Emitter};
use parse_js::ast::stmt::Stmt;

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
    let canonical = emit_with_mode(stmt, EmitMode::Canonical);
    assert_eq!(canonical, *expected_output);

    // Ensure the emitted text parses as valid TypeScript.
    parse_ts(&canonical);
  }

  let mut all_emitter = Emitter::new(EmitOptions::canonical());
  emit_top_level(&mut all_emitter, parsed.stx.as_ref()).expect("full emit");
  let all = String::from_utf8(all_emitter.into_bytes()).expect("utf8");
  assert_eq!(all, expected.join("\n"));

  // Spot-check minified output.
  let minified_expected = [
    "export declare interface Foo {}",
    "declare namespace A.B.C{}",
    "declare module \"x\"{interface Foo {}}",
    "declare global{interface Foo {}}",
    "type T = string | number;",
    "const enum E{A,B}",
  ];
  for (stmt, expected_output) in parsed.stx.body.iter().zip(minified_expected.iter()) {
    let minified = emit_with_mode(stmt, EmitMode::Minified);
    assert_eq!(minified, *expected_output);
  }
}

fn emit_with_mode(stmt: &parse_js::ast::node::Node<Stmt>, mode: EmitMode) -> String {
  let mut emitter = Emitter::new(EmitOptions::from(mode));
  emit_ts_stmt(&mut emitter, stmt).expect("emit succeeded");
  String::from_utf8(emitter.into_bytes()).expect("utf8")
}
