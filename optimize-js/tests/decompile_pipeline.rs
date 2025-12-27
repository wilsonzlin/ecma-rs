#[path = "common/mod.rs"]
mod common;

use common::compile_source;
use emit_js::EmitOptions;
use optimize_js::decompile::program_to_js;
use optimize_js::{DecompileOptions, TopLevelMode};
use parse_js::parse;

fn emit_source(src: &str) -> Vec<u8> {
  let program = compile_source(src, TopLevelMode::Module, false);
  let opts = DecompileOptions::default();
  match program_to_js(&program, &opts, EmitOptions::minified()) {
    Ok(bytes) => bytes,
    Err(err) => {
      let ast = optimize_js::decompile::program_to_ast(&program, &opts);
      panic!("decompile program: {err:?}, ast: {ast:?}");
    }
  }
}

#[test]
fn emitted_js_is_parseable() {
  let src = r#"
    const limit = getLimit();
    let value = seed();
    if (value < limit) {
      value = step(value);
    } else {
      value = fallback(value);
    }
    while (check(value)) {
      value = step(value);
    }
    finish(value);
  "#;

  let emitted = emit_source(src);
  let emitted_str = String::from_utf8(emitted).expect("utf-8 output");
  parse(&emitted_str).expect("reparse emitted JS");
}

#[test]
fn emitted_js_is_deterministic() {
  let src = r#"
    let counter = 0;
    while (next(counter)) {
      counter = tick(counter);
    }
    counter;
  "#;

  let first = emit_source(src);
  let second = emit_source(src);
  assert_eq!(first, second, "decompiled output should be stable");
}
