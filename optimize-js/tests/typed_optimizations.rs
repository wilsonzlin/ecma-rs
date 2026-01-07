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

#[test]
fn typed_optional_chaining_is_elided_when_receiver_is_non_nullish() {
  let src = "let x = 1; console?.log(x);";
  let expected_src = "let x = 1; console.log(x);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_optional_chaining_is_elided_for_non_nullish_union() {
  let src = r#"
    let x: string | number = 1;
    console.log(x?.toString());
  "#;
  let expected_src = r#"
    let x: string | number = 1;
    console.log(x.toString());
  "#;

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_nullish_coalescing_is_elided_when_left_is_non_nullish() {
  let src = r#"
    declare function sideEffect(): number;
    console.log(console ?? sideEffect());
  "#;
  let expected_src = "console.log(console);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_null_check_is_folded_when_operand_cannot_be_nullish() {
  let src = r#"
    if (console === null) {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(2);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_null_check_loose_equality_is_folded_when_operand_cannot_be_nullish() {
  let src = r#"
    if (console == null) {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(2);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_null_check_loose_inequality_is_folded_when_operand_cannot_be_nullish() {
  let src = r#"
    if (console != null) {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(1);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_null_check_strict_inequality_is_folded_when_operand_cannot_be_nullish() {
  let src = r#"
    if (console !== null) {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(1);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_null_check_strict_equality_with_undefined_is_folded_when_operand_cannot_be_nullish() {
  let src = r#"
    if (console === undefined) {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(2);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_if_condition_literal_false_elides_then_branch() {
  let src = r#"
    if (alwaysFalse()) {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "alwaysFalse();console.log(2);";

  let mut host = typecheck_ts::MemoryHost::new();
  let input = typecheck_ts::FileKey::new("input.ts");
  let decls = typecheck_ts::FileKey::new("decls.d.ts");
  host.insert(input.clone(), src);
  host.insert(decls.clone(), "declare function alwaysFalse(): false;");
  let tc_program = Arc::new(typecheck_ts::Program::new(host, vec![input.clone(), decls]));
  let _ = tc_program.check();
  let file_id = tc_program.file_id(&input).expect("typecheck file id");

  let typed_program = optimize_js::compile_source_with_typecheck(
    src,
    TopLevelMode::Module,
    false,
    tc_program,
    file_id,
  )
  .expect("compile with type info");
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_typeof_check_is_folded_when_operand_type_is_known() {
  let src = r#"
    let s: string = "x";
    if (typeof s === "string") {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(1);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_typeof_check_is_folded_for_string_literal_union() {
  let src = r#"
    let s: "a" | "b" = "a";
    if (typeof s === "string") {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(1);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_typeof_check_strict_inequality_is_folded_when_operand_type_is_known() {
  let src = r#"
    let s: string = "x";
    if (typeof s !== "string") {
      console.log(1);
    } else {
      console.log(2);
    }
  "#;
  let expected_src = "console.log(2);";

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_mode_is_noop_when_type_info_is_unavailable() {
  let src = "let x = 1; console?.log(x);";

  let untyped_program = compile_source(src, TopLevelMode::Module, false);
  let untyped_out = emit(&untyped_program);

  let mut host = typecheck_ts::MemoryHost::new();
  let file = typecheck_ts::FileKey::new("other.ts");
  host.insert(file.clone(), "export {}");
  let tc_program = Arc::new(typecheck_ts::Program::new(host, vec![file.clone()]));
  let _ = tc_program.check();
  let file_id = tc_program.file_id(&file).expect("typecheck file id");

  let typed_program = optimize_js::compile_source_with_typecheck(
    src,
    TopLevelMode::Module,
    false,
    tc_program,
    file_id,
  )
  .expect("compile with mismatched type info");

  assert_eq!(emit(&typed_program), untyped_out);
}

#[test]
fn typed_optimizations_work_with_nonzero_type_file_ids() {
  let src = "let x = 1; console?.log(x);";
  let expected_src = "let x = 1; console.log(x);";

  let mut host = typecheck_ts::MemoryHost::new();
  let dummy = typecheck_ts::FileKey::new("file0.ts");
  let input = typecheck_ts::FileKey::new("file1.ts");
  host.insert(dummy.clone(), "export {}");
  host.insert(input.clone(), src);
  let tc_program = Arc::new(typecheck_ts::Program::new(
    host,
    vec![dummy.clone(), input.clone()],
  ));
  let _ = tc_program.check();
  let file_id = tc_program.file_id(&input).expect("typecheck file id");
  assert_eq!(file_id, typecheck_ts::FileId(1));

  let typed_program = optimize_js::compile_source_with_typecheck(
    src,
    TopLevelMode::Module,
    false,
    tc_program,
    file_id,
  )
  .expect("compile with type info");
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_info_is_disabled_when_source_text_mismatches_type_program_file() {
  let type_src = "let x = 1; console?.log(x);";
  // Same length as `console` so expression spans line up, but should not inherit
  // types from the `type_src` program.
  let src = "let x = 1; consule?.log(x);";

  let untyped_program = compile_source(src, TopLevelMode::Module, false);
  let untyped_out = emit(&untyped_program);

  let mut host = typecheck_ts::MemoryHost::new();
  let file = typecheck_ts::FileKey::new("file0.ts");
  host.insert(file.clone(), type_src);
  let tc_program = Arc::new(typecheck_ts::Program::new(host, vec![file.clone()]));
  let _ = tc_program.check();
  let file_id = tc_program.file_id(&file).expect("typecheck file id");
  assert_eq!(file_id, typecheck_ts::FileId(0));

  let typed_program = optimize_js::compile_source_with_typecheck(
    src,
    TopLevelMode::Module,
    false,
    tc_program,
    file_id,
  )
  .expect("compile with mismatched type program");

  assert_eq!(emit(&typed_program), untyped_out);
}

#[test]
fn typed_truthiness_folds_if_conditions() {
  let src = r#"
    declare function getObj(): {};
    declare function empty(): "";
    declare function nonEmpty(): "x";
    declare function zero(): 0;
    declare function one(): 1;
    declare function a(): void;
    declare function b(): void;

    if (getObj()) {
      a();
    } else {
      b();
    }
    if (empty()) {
      a();
    } else {
      b();
    }
    if (nonEmpty()) {
      a();
    } else {
      b();
    }
    if (zero()) {
      a();
    } else {
      b();
    }
    if (one()) {
      a();
    } else {
      b();
    }
  "#;
  let expected_src = r#"
    declare function getObj(): {};
    declare function empty(): "";
    declare function nonEmpty(): "x";
    declare function zero(): 0;
    declare function one(): 1;
    declare function a(): void;
    declare function b(): void;

    getObj();
    a();
    empty();
    b();
    nonEmpty();
    a();
    zero();
    b();
    one();
    a();
  "#;

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_truthiness_folds_conditional_expressions() {
  let src = r#"
    declare function empty(): "";
    declare function nonEmpty(): "x";
    declare function a(): void;
    declare function b(): void;

    empty() ? a() : b();
    nonEmpty() ? a() : b();
  "#;
  let expected_src = r#"
    declare function empty(): "";
    declare function nonEmpty(): "x";
    declare function a(): void;
    declare function b(): void;

    empty();
    b();
    nonEmpty();
    a();
  "#;

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}

#[test]
fn typed_truthiness_folds_logical_expressions() {
  let src = r#"
    declare function alwaysTrue(): true;
    declare function alwaysFalse(): false;
    declare function sideEffect(): void;

    alwaysTrue() && sideEffect();
    alwaysFalse() && sideEffect();
    alwaysTrue() || sideEffect();
    alwaysFalse() || sideEffect();
  "#;
  let expected_src = r#"
    declare function alwaysTrue(): true;
    declare function alwaysFalse(): false;
    declare function sideEffect(): void;

    alwaysTrue();
    sideEffect();
    alwaysFalse();
    alwaysTrue();
    alwaysFalse();
    sideEffect();
  "#;

  let typed_program = compile_source_typed(src, TopLevelMode::Module, false);
  let expected_program = compile_source(expected_src, TopLevelMode::Module, false);

  assert_eq!(emit(&typed_program), emit(&expected_program));
}
