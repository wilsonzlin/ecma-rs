#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn for_await_of_statements_are_supported() {
  let src = r#"
    const xs = getAsyncIterator();
    for await (const x of xs) {
      console.log(x);
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

  assert!(
    !js.contains("__optimize_js_await"),
    "await marker should not leak into output: {js}"
  );
  parse_js::parse(js).expect("emitted JS should parse");
}

