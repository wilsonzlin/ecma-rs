#![cfg(feature = "typed")]

#[path = "common/mod.rs"]
mod common;

use common::{compile_source, compile_source_typed};
use emit_js::EmitOptions;
use optimize_js::decompile::program_to_js;
use optimize_js::{DecompileOptions, TopLevelMode};
use std::sync::Arc;

fn normalize_registers(js: &str) -> String {
  fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
  }

  let bytes = js.as_bytes();
  let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
  let mut map: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
  let mut next = 0usize;
  let mut i = 0usize;
  while i < bytes.len() {
    if bytes[i] == b'r' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
      let mut j = i + 1;
      while j < bytes.len() && bytes[j].is_ascii_digit() {
        j += 1;
      }
      let left_boundary = i == 0 || !is_ident_byte(bytes[i - 1]);
      let right_boundary = j == bytes.len() || !is_ident_byte(bytes[j]);
      if left_boundary && right_boundary {
        let key = &js[i..j];
        let id = *map.entry(key).or_insert_with(|| {
          let id = next;
          next += 1;
          id
        });
        out.push(b'r');
        out.extend_from_slice(id.to_string().as_bytes());
        i = j;
        continue;
      }
    }
    out.push(bytes[i]);
    i += 1;
  }
  String::from_utf8(out).expect("normalized JS should be UTF-8")
}

fn emit(program: &optimize_js::Program) -> String {
  let bytes = program_to_js(
    program,
    &DecompileOptions::default(),
    EmitOptions::minified(),
  )
  .expect("emit optimized JS");
  normalize_registers(std::str::from_utf8(&bytes).expect("emitted JS should be UTF-8"))
}

const DETERMINISM_RUNS: usize = 10;

#[test]
fn typed_compile_output_is_deterministic_with_internal_typecheck() {
  let src = r#"
    /// <reference no-default-lib="true" />
    declare var console: { log: any };
    declare function alwaysFalse(): false;
    declare function sideEffect(): number;
    let x: string = "x";
    console?.log(x);
    if (typeof x === "string") { console.log(1) } else { console.log(2) }
    console.log(x ?? sideEffect());
    if (alwaysFalse()) { console.log(3) } else { console.log(4) }
  "#;

  let _ = compile_source(src, TopLevelMode::Module, false);
  let expected = emit(&compile_source_typed(src, TopLevelMode::Module, false));
  for _ in 0..DETERMINISM_RUNS {
    let out = emit(&compile_source_typed(src, TopLevelMode::Module, false));
    assert_eq!(out, expected);
  }
}

#[test]
fn typed_compile_output_is_deterministic_with_external_typecheck_program() {
  let src = r#"
    /// <reference no-default-lib="true" />
    declare var console: { log: any };
    declare function alwaysFalse(): false;
    declare function sideEffect(): number;
    let x: string = "x";
    console?.log(x);
    if (typeof x === "string") { console.log(1) } else { console.log(2) }
    console.log(x ?? sideEffect());
    if (alwaysFalse()) { console.log(3) } else { console.log(4) }
  "#;

  let _ = compile_source(src, TopLevelMode::Module, false);
  let mut host = typecheck_ts::MemoryHost::new();
  let input = typecheck_ts::FileKey::new("input.ts");
  host.insert(input.clone(), src);
  let tc_program = Arc::new(typecheck_ts::Program::new(host, vec![input.clone()]));
  let _ = tc_program.check();
  let file_id = tc_program.file_id(&input).expect("typecheck file id");

  let expected = emit(
    &optimize_js::compile_source_with_typecheck(
      src,
      TopLevelMode::Module,
      false,
      Arc::clone(&tc_program),
      file_id,
    )
    .expect("compile with type info"),
  );
  for _ in 0..DETERMINISM_RUNS {
    let out = emit(
      &optimize_js::compile_source_with_typecheck(
        src,
        TopLevelMode::Module,
        false,
        Arc::clone(&tc_program),
        file_id,
      )
      .expect("compile with type info"),
    );
    assert_eq!(out, expected);
  }
}
