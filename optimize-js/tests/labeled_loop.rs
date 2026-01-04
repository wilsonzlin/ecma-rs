#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn labeled_break_and_continue_are_supported_for_loops() {
  let src = r#"
    let i = 0;
    outer: while (i < 10) {
      i += 1;
      let j = 0;
      while (j < 10) {
        j += 1;
        if (j === 3) continue outer;
        if (j === 4) break outer;
      }
      console.log(i);
    }
  "#;

  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  parse_js::parse(js).expect("emitted JS should parse");
}
