#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn array_literals_are_supported() {
  let src = "console.log([1,,2]);";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_array"),
    "internal array helper leaked into output: {js}"
  );
  assert!(
    !js.contains("__optimize_js_array_hole"),
    "internal array hole helper leaked into output: {js}"
  );
  assert!(
    js.contains("[1,,2]"),
    "expected array literal in output: {js}"
  );
}
