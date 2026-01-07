#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn for_in_statements_are_supported() {
  let src = r#"
    const obj = { a: 1, b: 2 };
    let total = 0;
    for (const key in obj) {
      total += obj[key];
    }
    console.log(total);
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
