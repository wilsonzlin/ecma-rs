#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use emit_js::EmitOptions;
use optimize_js::decompile::{program_to_js, DecompileOptions, TempDeclStyle};
use optimize_js::TopLevelMode;

#[test]
fn var_bindings_are_initialized_to_undefined_before_first_use() {
  let src = "console.log(x); var x = 1;";
  let program = compile_source(src, TopLevelMode::Module, false);

  let opts = DecompileOptions {
    temp_decl_style: TempDeclStyle::LetWithVoidInit,
    ..DecompileOptions::default()
  };
  let bytes =
    program_to_js(&program, &opts, EmitOptions::minified()).expect("decompile program to JS");
  let out = String::from_utf8(bytes).expect("emitted JS should be UTF-8");

  parse_js::parse(&out).expect("emitted JS should parse");
  if let Err(errs) = optimize_js::compile_source(&out, TopLevelMode::Module, false) {
    panic!("compile emitted JS: {errs:?}\n\n{out}");
  }
}
