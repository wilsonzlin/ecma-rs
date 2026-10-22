//! Union object spreads distribute like tsc `getSpreadType`: `{ ...u }` with
//! `u: A | B` is `spread(A) | spread(B)` (cross-product across multiple
//! union spreads), nullish members contribute nothing, and later literal
//! members *replace* earlier spread members with the same key
//! (`spreadUnion.ts`, `spreadUnion2.ts`).

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
fn union_spread_matches_declared_union() {
  let src = "var union: { a: number } | { b: string };\nvar o3: { a: number } | { b: string };\nvar o3 =  { ...union };\n";
  assert_eq!(codes(src), ["TS2454"]);
}

#[test]
fn union_spread_with_extra_prop() {
  let src = "var union: { a: number } | { b: string };\nvar o4: { a: boolean } | { b: string , a: boolean};\nvar o4 =  { ...union, a: false };\n";
  assert_eq!(codes(src), ["TS2454"]);
}

#[test]
fn double_union_spread_cross_product() {
  let src = "var union: { a: number } | { b: string };\nvar o5: { a: number } | { b: string } | { a: number, b: string };\nvar o5 =  { ...union, ...union };\n";
  assert_eq!(codes(src), ["TS2454", "TS2454"]);
}

#[test]
fn nullish_spread_members_contribute_nothing() {
  let src = "declare const undefinedUnion: { a: number } | undefined;\nvar o1: { a: number };\nvar o1 = { ...undefinedUnion };\n";
  assert!(codes(src).is_empty());
}

#[test]
fn later_prop_replaces_spread_member() {
  let src = "var p = { a: 1 };\nvar q = { ...p, a: 'x' };\nvar s: string = q.a;\n";
  assert!(codes(src).is_empty());
}
