//! Fractional numeric property keys (`{ 1.1: string }`) are string keys, not
//! `PropKey::Number(i64)` — i64 parsing fails for non-integers, which used to
//! drop the member from the shape entirely (or collapse it to key `0` in
//! flow-built object literals). `a[1.1]` must find the member
//! (`objectTypeWithNumericProperty.ts`).

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
fn fractional_numeric_prop_in_object_type_annotation() {
  // No TS2403: `a[1.1]` must be `string` (not dropped-to-unknown), matching
  // `b[1.1]` from the object literal. TS2454 on `a` is tsc-correct behavior
  // for `var a: T;` used before assignment, so assert full equality.
  let src = "var a: { 1: number; 1.1: string };\nvar r2 = a[1.1];\nvar b = { 1: 1, 1.1: '' };\nvar r2 = b[1.1];";
  assert_eq!(codes(src), ["TS2454"]);
}

#[test]
fn fractional_numeric_prop_kept_in_type_literals() {
  // The member must exist: indexing it and assigning to the wrong type fails.
  let src = "declare const a: { 1: number; 1.1: string };\nconst n: number = a[1.1];";
  assert_eq!(codes(src), ["TS2322"]);
  // String-spelled index finds the same member.
  let src2 = "declare const a: { 1: number; 1.1: string };\nconst n: number = a['1.1'];";
  assert_eq!(codes(src2), ["TS2322"]);
}

#[test]
fn integer_numeric_props_unaffected() {
  let src = "declare const a: { 1: number; 1.1: string };\nconst s: string = a[1];";
  assert_eq!(codes(src), ["TS2322"]);
  // And the right types line up cleanly.
  let src2 = "declare const a: { 1: number; 1.1: string };\nconst n: number = a[1];\nconst s: string = a[1.1];";
  assert!(codes(src2).is_empty());
}

#[test]
fn fractional_key_in_object_literal_not_collapsed_to_zero() {
  // Flow-built object-literal shapes: `1.1` must not become key `0`.
  let src = "const l = { 1.1: '' };\nl['1.1'].toUpperCase();";
  assert!(codes(src).is_empty());
  // A collapsed-to-`0` key would collide with a real `0` member instead.
  let src2 =
    "const l = { 0: true, 1.1: '' };\nconst b: boolean = l[0];\nconst s: string = l['1.1'];";
  assert!(codes(src2).is_empty());
}
