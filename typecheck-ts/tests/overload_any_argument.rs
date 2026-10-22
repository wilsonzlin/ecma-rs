//! Overload resolution with `any` arguments: tsc prefers an overload whose
//! parameter is `any` over concrete-parameter overloads
//! (`anyAssignabilityInInheritance.ts` — "any is not a subtype of number so it
//! skips that overload, is a subtype of itself so it picks second; if truly
//! ambiguous it would pick first overload").

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
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

#[test]
fn any_argument_prefers_any_param_overload() {
  // Both calls resolve to the `any` overload, so both `r3` are `any` and the
  // redeclaration is clean (no TS2403).
  let src = r#"declare function foo2(x: number): number;
declare function foo2(x: any): any;
declare const a: any;
var r3 = foo2(a);
declare function foo3(x: string): string;
declare function foo3(x: any): any;
var r3 = foo3(a);
"#;
  assert!(codes(src).is_empty());
}

#[test]
fn any_param_overload_return_type_is_any() {
  // If the number overload were picked, `r` would be `number` and the string
  // assignment would fail; tsc picks the any overload (`r: any`).
  let src = r#"declare function f(x: number): number;
declare function f(x: any): any;
declare const a: any;
const r = f(a);
const s: string = r;
"#;
  assert!(codes(src).is_empty());
}

#[test]
fn no_any_param_overload_keeps_first_match() {
  // Truly ambiguous for an `any` argument: first overload wins (`number`).
  let src = r#"declare function f(x: number): number;
declare function f(x: string): string;
declare const a: any;
const r = f(a);
const n: number = r;
"#;
  assert!(codes(src).is_empty());
}

#[test]
fn non_any_argument_unaffected() {
  // A `number` argument picks the number overload (first match as before).
  let src = r#"declare function f(x: number): number;
declare function f(x: any): any;
declare const a: number;
const r = f(a);
const n: number = r;
"#;
  assert!(codes(src).is_empty());
}
