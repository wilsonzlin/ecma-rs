#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn debugger_statements_are_ignored() {
  let src = r#"
    let x = 0;
    debugger;
    x += 1;
    if (x > 0) {
      debugger;
      x += 1;
    }
    console.log(x);
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
