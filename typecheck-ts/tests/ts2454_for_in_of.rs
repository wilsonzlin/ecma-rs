//! TS2454 used-before-assignment around for-in / for-of.
//!
//! Oracle: tsc 5.9.3 (`typecheck-ts-harness` pin) under `--strict`.
//! - `any` / `unknown` / `void` / `T | undefined` declared types are DA-exempt
//!   (tsc `assumeInitialized` / `containsUndefinedType`).
//! - for-in/of LHS assignment is definite inside the loop body, not after.
//! - Same-body unassigned RHS of for-in/of still reports TS2454.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn check(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut diags: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2454")
    .map(|d| {
      format!(
        "{}:{}-{}: {}",
        d.code, d.primary.range.start, d.primary.range.end, d.message
      )
    })
    .collect();
  diags.sort();
  diags
}

fn messages_mentioning<'a>(diags: &'a [String], name: &str) -> Vec<&'a String> {
  diags.iter().filter(|m| m.contains(name)).collect()
}

/// Upstream `controlFlow/controlFlowForInStatement.ts`: `obj: any` on the
/// for-in RHS must not get TS2454; `cond: boolean` still does (twice).
#[test]
fn for_in_rhs_any_exempt_but_unassigned_cond_reports() {
  let src = r#"
let x: string | number | boolean | RegExp | Function;
let obj: any;
let cond: boolean;

x = /a/;
for (let y in obj) {
    x = y;
    if (cond) {
        x = 42;
        continue;
    }
    if (cond) {
        x = true;
        break;
    }
}
x;
"#;
  let d = check(src);
  assert!(
    messages_mentioning(&d, "obj").is_empty(),
    "false positive on for-in RHS obj:any: {d:?}"
  );
  assert_eq!(
    messages_mentioning(&d, "cond").len(),
    2,
    "expected two cond TS2454 (tsc oracle): {d:?}"
  );
}

/// Upstream `es6/for-ofStatements/for-of24.ts`.
#[test]
fn for_of_rhs_var_any_exempt() {
  let src = "var x: any;\nfor (var v of x) { }\n";
  let d = check(src);
  assert!(
    d.is_empty(),
    "false positive for-of24 (var x: any RHS): {d:?}"
  );
}

/// Same-body unassigned non-exempt RHS still reports (restores under-report).
#[test]
fn for_of_rhs_unassigned_array_reports() {
  let src = r#"
function f() {
  let obj: number[];
  let x: string | number;
  x = 1;
  for (x of obj) { x; }
  x;
}
"#;
  let d = check(src);
  assert_eq!(
    messages_mentioning(&d, "obj").len(),
    1,
    "expected TS2454 on for-of RHS obj:number[]: {d:?}"
  );
  assert!(
    messages_mentioning(&d, "x is").is_empty(),
    "false positive on assigned for-of LHS x: {d:?}"
  );
}

#[test]
fn for_in_rhs_unassigned_object_reports() {
  let src = r#"
function f() {
  let obj: object;
  for (const k in obj) { k; }
}
"#;
  let d = check(src);
  assert_eq!(
    messages_mentioning(&d, "obj").len(),
    1,
    "expected TS2454 on for-in RHS: {d:?}"
  );
}

#[test]
fn for_of_lhs_assigned_inside_not_after() {
  let src = r#"
declare const arr: string[];
function f() {
  let x: string;
  for (x of arr) {
    let y: string = x;
  }
  return x;
}
"#;
  let d = check(src);
  assert!(
    messages_mentioning(&d, "x is").len() == 1,
    "use after for-of must TS2454; inside must not: {d:?}"
  );
}

#[test]
fn for_of_decl_binding_inside_ok() {
  let src = r#"
declare const arr: string[];
function f() {
  for (const x of arr) {
    let y: string = x;
  }
}
"#;
  let d = check(src);
  assert!(d.is_empty(), "false positive on for-of decl binding: {d:?}");
}

#[test]
fn string_or_undefined_annotation_exempt() {
  let src = r#"
function f() {
  let u: string | undefined;
  return u;
}
"#;
  let d = check(src);
  assert!(
    d.is_empty(),
    "tsc exempts annotations that include undefined: {d:?}"
  );
}
