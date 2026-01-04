#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

fn emit(program: &optimize_js::Program) -> Vec<u8> {
  program_to_js(
    program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS")
}

#[test]
fn ts_only_expression_wrappers_are_erased() {
  let src = "let x = unknownVar as any; console.log(x!, unknownVar satisfies any);";
  let expected_src = "let x = unknownVar; console.log(x, unknownVar);";

  let program = compile_source(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&program), emit(&expected_program));
}
