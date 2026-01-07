#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn template_literals_are_supported() {
  let src = "console.log(`a${1}b${2}c`);";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_template"),
    "internal template helper leaked into output: {js}"
  );
  assert!(
    js.contains("`a${1}b${2}c`"),
    "expected template literal in output: {js}"
  );
}

#[test]
fn tagged_templates_are_supported() {
  let src = "console.log(String.raw`a${1}b`);";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_tagged_template"),
    "internal tagged template helper leaked into output: {js}"
  );
  assert!(
    js.contains("String.raw"),
    "expected tag expression in output: {js}"
  );
  assert!(
    js.contains("`a${1}b`"),
    "expected tagged template literal in output: {js}"
  );
}
