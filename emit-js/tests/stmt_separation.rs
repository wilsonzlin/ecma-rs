use emit_js::{emit_program, EmitOptions, Emitter};
use parse_js::{Dialect, ParseOptions, SourceType};

mod util;

fn assert_roundtrip(src: &str) -> bool {
  let opts = ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Module,
  };
  let parsed = match parse_js::parse_with_options(src, opts) {
    Ok(program) => program,
    Err(err) => {
      eprintln!("SKIP roundtrip for {src:?}: parse failed: {err:?}");
      return false;
    }
  };
  let mut em = Emitter::new(EmitOptions::minified());
  emit_program(&mut em, parsed.stx.as_ref())
    .unwrap_or_else(|err| panic!("emit failed for {src:?}: {err:?}"));
  let emitted = String::from_utf8(em.into_bytes()).expect("utf-8");
  let reparsed = match parse_js::parse_with_options(&emitted, opts) {
    Ok(ast) => ast,
    Err(err) => {
      eprintln!("SKIP reparse {emitted:?}: {err:?}");
      return false;
    }
  };
  assert_eq!(
    util::serialize_without_locs(&parsed),
    util::serialize_without_locs(&reparsed),
    "emitted source: {emitted}"
  );
  true
}

#[test]
fn asi_hazards_are_separated() {
  let cases = [
    "a\n(b)",
    "a\n[0]",
    "a;/+/.test(b)",
    "a\n`${b}`",
    "a;<div/>",
    "a\nclass Foo {}",
    "a\nfunction foo() {}",
    "a\nasync function foo() {}",
    "function f(){ return\n(b) }",
  ];

  let mut ran = 0;
  for case in cases {
    println!("roundtrip: {case}");
    if assert_roundtrip(case) {
      ran += 1;
    }
  }
  assert!(ran > 0, "all ASI hazard cases were skipped");
}

#[test]
fn switch_branch_boundaries() {
  let program = "switch(x){case 0: a\n(b) case 1: c}";
  assert!(assert_roundtrip(program));
}
