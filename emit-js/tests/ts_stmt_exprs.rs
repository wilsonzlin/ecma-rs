use emit_js::{emit_top_level_stmt, EmitMode, EmitOptions, Emitter};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;

mod util;

fn parse_ts(source: &str) -> Node<TopLevel> {
  parse_js::parse(source).expect("source should parse")
}

fn emit_ts(top: &Node<TopLevel>, mode: EmitMode) -> String {
  let mut emitter = Emitter::new(EmitOptions::from(mode));
  emit_top_level_stmt(&mut emitter, top.stx.as_ref()).expect("emit succeeded");
  String::from_utf8(emitter.into_bytes()).expect("utf8")
}

fn assert_roundtrip(source: &str, mode: EmitMode, expected: &str) {
  let parsed = parse_ts(source);
  let emitted = emit_ts(&parsed, mode);
  assert_eq!(emitted, expected);

  let reparsed = parse_ts(&emitted);
  assert_eq!(
    util::serialize_without_locs(&parsed),
    util::serialize_without_locs(&reparsed)
  );
}

#[test]
fn emits_enum_computed_initializer() {
  let source = "enum E { A = 1 + 2 }";
  assert_roundtrip(source, EmitMode::Canonical, "enum E { A= 1+2 }");
  assert_roundtrip(source, EmitMode::Minified, "enum E{A=1+2}");
}

#[test]
fn emits_enum_initializer_with_arrow_block_body() {
  let source = "enum E { A = (() => { return 1 })() }";
  assert_roundtrip(
    source,
    EmitMode::Canonical,
    "enum E { A= (()=>{return 1;})() }",
  );
  assert_roundtrip(source, EmitMode::Minified, "enum E{A=(()=>{return 1;})()}");
}

#[test]
fn emits_namespace_value_initializer() {
  let source = "namespace N { export const x = 1 + 2; }";
  assert_roundtrip(
    source,
    EmitMode::Canonical,
    "namespace N { export const x=1+2; }",
  );
  assert_roundtrip(
    source,
    EmitMode::Minified,
    "namespace N{export const x=1+2;}",
  );
}

#[test]
fn emits_export_assignment_with_optional_chain_and_object_methods() {
  let source = "export = foo?.bar ?? { get x() { return 1 }, set x(v) {}, method() {} };";
  assert_roundtrip(
    source,
    EmitMode::Canonical,
    "export = foo?.bar??{get x(){return 1;},set x(v){},method(){}};",
  );
  assert_roundtrip(
    source,
    EmitMode::Minified,
    "export=foo?.bar??{get x(){return 1;},set x(v){},method(){}};",
  );
}

#[test]
fn emits_export_assignment_with_class_expression() {
  let source = "export = class { method() { return 1 } };";
  assert_roundtrip(
    source,
    EmitMode::Canonical,
    "export = class{method(){return 1;}};",
  );
  assert_roundtrip(
    source,
    EmitMode::Minified,
    "export=class{method(){return 1;}};",
  );
}
