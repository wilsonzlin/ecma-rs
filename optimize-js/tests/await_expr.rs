#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn await_expressions_are_supported() {
  let src = "await 1;";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_await"),
    "internal await helper leaked into output: {js}"
  );
  assert!(
    js.contains("await 1"),
    "expected await expression in output: {js}"
  );
  parse_js::parse(js).expect("emitted JS should parse");
}
