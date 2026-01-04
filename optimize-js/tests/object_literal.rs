#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use optimize_js::{program_to_js, DecompileOptions, TopLevelMode};

#[test]
fn object_literals_are_supported() {
  let src = "console.log({a:1,b:2});";
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    !js.contains("__optimize_js_object"),
    "internal object helper leaked into output: {js}"
  );
  assert!(
    !js.contains("__optimize_js_object_prop"),
    "internal object prop helper leaked into output: {js}"
  );
  assert!(
    !js.contains("__optimize_js_object_spread"),
    "internal object spread helper leaked into output: {js}"
  );
  assert!(
    js.contains("{a:1,b:2}"),
    "expected object literal in output: {js}"
  );
}

#[test]
fn computed_object_keys_are_preserved() {
  let src = r#"console.log({["__proto__"]:1});"#;
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    js.contains("{[\"__proto__\"]:1}"),
    "expected computed key to be preserved: {js}"
  );
}

#[test]
fn string_object_keys_that_are_not_identifiers_are_quoted() {
  let src = r#"console.log({"a b":1});"#;
  let program = compile_source(src, TopLevelMode::Module, false);

  let bytes = program_to_js(
    &program,
    &DecompileOptions::default(),
    emit_js::EmitOptions::minified(),
  )
  .expect("emit JS");
  let js = std::str::from_utf8(&bytes).expect("UTF-8 output");

  assert!(
    js.contains("{\"a b\":1}"),
    "expected string key to remain quoted: {js}"
  );
  assert!(
    !js.contains("{a b:1}"),
    "expected quoted key, got invalid identifier-like key: {js}"
  );
}
