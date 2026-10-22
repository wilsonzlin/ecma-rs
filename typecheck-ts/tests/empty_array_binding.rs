//! Empty array literal bindings vs tsc (`getTypeForVariableLikeDeclaration` /
//! `checkArrayLiteral` / `getWidenedType`):
//!
//! - `--noImplicitAny` on: evolving `autoArrayType` (`any[]`); `push` is not an
//!   error. (We do not evolve the element type per push; it stays `any[]`.)
//! - `--noImplicitAny` off + `--strictNullChecks` on: binding keeps the
//!   synthesized `never[]`; `push` errors TS2345.
//! - `--noImplicitAny` off + `--strictNullChecks` off: the synthesized
//!   `undefinedWideningType[]` widens to `any[]` for the declaration; `push`
//!   is not an error.
//!
//! Return/argument positions are unaffected by `noImplicitAny`: bare `[]`
//! synthesizes `never[]` under `strictNullChecks` (tsc `checkArrayLiteral`).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

fn opts(strict_null_checks: bool, no_implicit_any: bool) -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = strict_null_checks;
  opts.no_implicit_any = no_implicit_any;
  opts
}

const BINDING_SRC: &str = r#"
const array = [];
for (let i = 0; i < 10; ++i) {
  array.push(class C {
    [i] = () => C;
    static [i] = 100;
  });
}
array.push(1);
"#;

#[test]
fn binding_position_never_array_under_strict_null_checks() {
  // tsc default-ish strictness (SNC on, NIA off): `never[]`, push is TS2345.
  let c = codes(opts(true, false), BINDING_SRC);
  assert!(
    c.iter().any(|x| x == "TS2345"),
    "expected TS2345 pushing into never[] under SNC+NIA-off: {c:?}"
  );
}

#[test]
fn binding_position_evolving_any_array_under_no_implicit_any() {
  // `computedPropertyNames52.ts` shape; valid under `--noImplicitAny`.
  assert_eq!(codes(opts(true, true), BINDING_SRC), Vec::<String>::new());
  assert_eq!(codes(opts(false, true), BINDING_SRC), Vec::<String>::new());
}

#[test]
fn binding_position_any_array_without_strict_null_checks() {
  // tsc `getWidenedType`: `undefinedWideningType[]` widens to `any[]` for the
  // declaration, so `push` is fine even with NIA off.
  assert_eq!(codes(opts(false, false), BINDING_SRC), Vec::<String>::new());
}

#[test]
fn empty_array_return_position_is_never() {
  let src = r#"
function f() {
  return [];
}
const r = f();
r.push(1);
"#;
  let c = codes(opts(true, false), src);
  assert!(
    c.iter().any(|x| x == "TS2345"),
    "expected TS2345 pushing into never[] return: {c:?}"
  );
}
