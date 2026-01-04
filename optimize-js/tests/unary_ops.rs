#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn compiles_not_plus_and_void() {
  // Regression test: these unary operators should be supported by the HIR->IL lowering.
  let src = "console.log(!true, +1, void 0);";
  let _program = compile_source(src, TopLevelMode::Module, false);
}

#[test]
fn delete_operator_is_lowered_without_internal_helpers() {
  let src = "delete unknownObj.prop;";
  let program = compile_source(src, TopLevelMode::Module, false);
  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_delete"),
    "internal delete helper leaked into output: {js}"
  );
  assert!(
    js.contains("delete"),
    "expected delete operator in output: {js}"
  );
}
