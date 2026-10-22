//! `for (k in obj)` accepts mapped types (`obj: { [P in K]: T }`) — tsc treats
//! mapped types as object types for the for-in RHS check
//! (`types/keyof/keyofAndForIn.ts`).

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
fn for_in_over_generic_mapped_type() {
  let src = "function f1<K extends string, T>(obj: { [P in K]: T }, k: K) {\n    let k1: K;\n    for (k1 in obj) {\n        let x1 = obj[k1];\n    }\n    for (let k2 in obj) {\n        let x2 = obj[k2];\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn for_in_over_mapped_keyof_type() {
  let src = "function f2<T>(obj: { [P in keyof T]: T[P] }, k: keyof T) {\n    let k1: keyof T;\n    for (k1 in obj) {\n        let x1 = obj[k1];\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn for_in_over_primitive_still_errors() {
  let src = "declare var n: number;\nfor (const k in n) {\n}\n";
  assert_eq!(codes(src), ["TS2407"]);
}
