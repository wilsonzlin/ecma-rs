use emit_js::{emit_program, EmitOptions, Emitter};
use parse_js::{Dialect, ParseOptions, SourceType};
use serde_json::to_value;

fn assert_roundtrip(src: &str) {
  let opts = ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Module,
  };
  let parsed = parse_js::parse_with_options(src, opts).expect("parse");
  let mut em = Emitter::new(EmitOptions::minified());
  emit_program(&mut em, parsed.stx.as_ref())
    .unwrap_or_else(|err| panic!("emit failed for {src:?}: {err:?}"));
  let emitted = String::from_utf8(em.into_bytes()).expect("utf-8");
  let reparsed = parse_js::parse_with_options(&emitted, opts).expect("reparse");
  assert_eq!(
    to_value(&parsed).unwrap(),
    to_value(&reparsed).unwrap(),
    "emitted source: {emitted}"
  );
}

#[test]
fn asi_hazards_are_separated() {
  let cases = [
    "a\n(b)",
    "a\n[0]",
    "a;/+/.test(b)",
    "a\n`b`",
    "a;<div/>",
    "a\nclass Foo {}",
    "a\nfunction foo() {}",
    "a\nasync function foo() {}",
    "function f(){ return\n(b) }",
  ];

  for case in cases {
    println!("roundtrip: {case}");
    assert_roundtrip(case);
  }
}

#[test]
fn switch_branch_boundaries() {
  let program = "switch(x){case 0: a\n(b) case 1: c}";
  assert_roundtrip(program);
}
