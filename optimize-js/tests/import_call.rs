#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn import_calls_are_supported() {
  let src = r#"console.log(import("./foo"));"#;
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    js.contains("import(\"./foo\")"),
    "expected import() call in output: {js}"
  );
  parse_js::parse(js).expect("emitted JS should parse");
}

