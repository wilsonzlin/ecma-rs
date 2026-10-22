//! TS2403 ("subsequent variable declarations must have the same type")
//! compares with tsc's `isTypeIdenticalTo` — structural identity, not `TypeId`
//! equality. A class instance and a structurally equal object type are "the
//! same type", so `var p: {x, y}; var p = new Point()` does not fire
//! (`AmbientModuleAndAmbientWithSameNameAndCommonRoot`). `any` is strict:
//! identical only to `any`, so `var a: any; var a: string` still fires.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
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
fn class_instance_is_identical_to_structural_object() {
  let src = r#"
class Point {
  constructor(x: number, y: number) {}
  x: number;
  y: number;
}
var p: { x: number; y: number; }
var p = new Point(0, 0);
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn any_is_only_identical_to_any() {
  let src = "var a: any;\nvar a: string;\n";
  assert!(codes(src).contains(&"TS2403".to_string()));
}

#[test]
fn distinct_primitives_still_fire() {
  let src = "var a: string;\nvar a: number;\n";
  assert!(codes(src).contains(&"TS2403".to_string()));
}

#[test]
fn identical_object_shapes_do_not_fire() {
  let src = "var a = { x: 1, y: 2 };\nvar a = { x: 3, y: 4 };\n";
  assert_eq!(codes(src), Vec::<String>::new());
}
