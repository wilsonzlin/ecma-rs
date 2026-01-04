#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn regex_literals_are_supported() {
  let src = "console.log(/a/g);";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_regex"),
    "internal regex helper leaked into output: {js}"
  );
  assert!(
    js.contains("/a/g"),
    "expected regex literal in output: {js}"
  );
}
