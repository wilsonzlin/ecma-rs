//! Empty array literal typing vs tsc (`never[]` under strictNullChecks).
//!
//! Bare `[]` synthesizes `never[]` (not `unknown[]`/`any[]`). That makes
//! `array.push(x)` a TS2345 when `--noImplicitAny` is off (conformance
//! `privateNameClassExpressionLoop.ts`), while contextual `T[]` sites still
//! accept `[]` because `never` is assignable to every `T`.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn program(opts: CompilerOptions, src: &str) -> (Program, diagnostics::FileId, String) {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  (program, file_id, src.to_string())
}

fn strict_no_implicit_any_off() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn bare_empty_array_is_never_array() {
  let src = "const array = [];\narray;\n";
  let (program, file_id, src) = program(strict_no_implicit_any_off(), src);
  let _ = program.check();
  let use_at = src.rfind("array;").expect("array use") as u32;
  let ty = program.type_at(file_id, use_at).expect("type at array");
  assert_eq!(
    program.display_type(ty).to_string(),
    "never[]",
    "bare [] under strictNullChecks must be never[]"
  );
}

#[test]
fn push_onto_bare_empty_array_is_ts2345() {
  // Mirrors privateNameClassExpressionLoop / tsc with noImplicitAny off:
  // Argument of type '…' is not assignable to parameter of type 'never'.
  let src = r#"
const array = [];
array.push(class C {
  #myField = "hello";
  #method() {}
  get #accessor() { return 42; }
  set #accessor(val) { }
});
"#;
  let (program, _, _) = program(strict_no_implicit_any_off(), src);
  let diagnostics = program.check();
  let hits: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == "TS2345")
    .collect();
  assert_eq!(hits.len(), 1, "expected one TS2345, got {diagnostics:?}");
  let d = hits[0];
  let snippet = &src[d.primary.range.start as usize..d.primary.range.end as usize];
  assert_eq!(snippet, "C", "tsc anchors TS2345 on the class name");
}

#[test]
fn contextual_empty_array_assigns_and_calls() {
  let src = r#"
let nums: number[] = [];
declare function take(xs: string[]): void;
take([]);
function ret(): boolean[] { return []; }
"#;
  let (program, file_id, src) = program(strict_no_implicit_any_off(), src);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "empty [] must be contextually acceptable as T[], got {diagnostics:?}"
  );
  let nums_at = src.find("nums").expect("nums") as u32;
  let ty = program.type_at(file_id, nums_at).expect("nums type");
  assert_eq!(program.display_type(ty).to_string(), "number[]");
}

#[test]
fn no_implicit_any_widens_empty_array_binding_to_any_array() {
  // tsc `autoArrayType`: under `--noImplicitAny`, empty-array bindings are
  // `any[]` (init still `never[]`), so `push` is not TS2345.
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  let src = "const array = [];\narray.push(1);\narray;\n";
  let (program, file_id, src) = program(opts, src);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == "TS2345" || d.code.as_str() == "TC3000"),
    "noImplicitAny empty [] should accept push (autoArrayType), got {diagnostics:?}"
  );
  let use_at = src.rfind("array;").expect("array use") as u32;
  let ty = program.type_at(file_id, use_at).expect("type at array");
  assert_eq!(
    program.display_type(ty).to_string(),
    "any[]",
    "binding must widen to any[] under noImplicitAny"
  );
}
