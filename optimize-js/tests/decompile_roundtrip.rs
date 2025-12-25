#![cfg(all(feature = "emit", feature = "decompile"))]

use emit_js::EmitOptions;
use optimize_js::{compile_source, decompile::program_to_js, DecompileOptions, TopLevelMode};

fn compile_and_emit(src: &str, mode: TopLevelMode) -> Vec<u8> {
  let program = compile_source(src, mode, false).expect("compile input");
  program_to_js(
    &program,
    &DecompileOptions::default(),
    EmitOptions::minified(),
  )
  .expect("decompile program to JS")
}

fn assert_roundtrip(src: &str, mode: TopLevelMode) {
  let out1 = compile_and_emit(src, mode);
  let out2 = compile_and_emit(src, mode);

  assert_eq!(out1, out2, "emitted JS should be deterministic");

  let out_str = String::from_utf8(out1).expect("emitted JS should be UTF-8");

  parse_js::parse(&out_str).expect("emitted JS should parse");
  compile_source(&out_str, mode, false).expect("emitted JS should recompile");
}

#[test]
fn decompile_roundtrip_module_mode() {
  let cases = [r#"
    let result = 0;
    const value = choose();
    if (value > 0) {
      if (check(value)) {
        result = run(value);
      } else {
        result = fallback(value);
      }
    } else {
      result = reset(result);
    }
  "#];

  for src in cases {
    assert_roundtrip(src, TopLevelMode::Module);
  }
}

#[test]
fn decompile_roundtrip_global_mode() {
  let cases = [
    r#"
      var total = 0;
      while (shouldContinue(total)) {
        total += 1;
        if (total > limit()) {
          break;
        }
      }
      for (;;) {
        total++;
        if (stop(total)) {
          break;
        }
      }
      finish(total);
    "#,
    r#"
      const currentTask = getTask();
      const items = getItems();
      const ctx = currentTask?.owner?.id;
      worker?.run?.(ctx, ...items, extraArg());
      report(worker?.getLast?.()?.result?.value);
    "#,
  ];

  for src in cases {
    assert_roundtrip(src, TopLevelMode::Global);
  }
}
