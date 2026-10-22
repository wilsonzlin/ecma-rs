use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn primitives_and_enum_assign_to_object() {
  let src = r#"
enum E { A }
var a: Object = 1;
var b: Object = true;
var c: Object = "a";
var d: Object = E.A;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "primitives/enum members should assign to Object, got {diags:?}"
  );
}

#[test]
fn overload_first_match_object_before_enum() {
  // `foo16(E.A)` must select `(x: Object) => Object`, not the later `(x: E) => E`.
  let src = r#"
enum E { A }
declare function foo16(x: Object): Object;
declare function foo16(x: E): E;
var r4 = foo16(E.A);
var ok: Object = r4;
var bad: E = r4;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let bad_at = src.find("bad").expect("bad") as u32;
  let ok_at = src.find("ok").expect("ok") as u32;
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .map(|d| d.primary.range.start)
    .collect();
  assert!(
    ts2322.iter().any(|&s| s == bad_at),
    "Object return should not assign to E, starts={ts2322:?} diags={diags:?}"
  );
  assert!(
    !ts2322.iter().any(|&s| s == ok_at),
    "Object return should assign to Object, starts={ts2322:?} diags={diags:?}"
  );
}

#[test]
fn distinct_numeric_enums_not_assignable() {
  let src = r#"
enum E { A }
enum E2 { A }
var a: E = E2.A;
var b: E2 = E.A;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    2,
    "distinct enums must not be mutually assignable, got {diags:?}"
  );
}

#[test]
fn distinct_enums_not_first_overload_match() {
  // foo13(E.A) must not pick `(x: E2) => E2` — distinct enums are not assignable.
  let src = r#"
enum E { A }
enum E2 { A }
declare function foo13(x: E2): E2;
declare function foo13(x: E): E;
var r4: E = foo13(E.A);
var bad: E2 = foo13(E.A);
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let bad_at = src.find("bad").expect("bad") as u32;
  let ok_at = src.find("r4").expect("r4") as u32;
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .map(|d| d.primary.range.start)
    .collect();
  assert!(
    !ts2322.iter().any(|&s| s == ok_at),
    "foo13(E.A) should return E, starts={ts2322:?} diags={diags:?}"
  );
  assert!(
    ts2322.iter().any(|&s| s == bad_at),
    "E return should not assign to E2, starts={ts2322:?} diags={diags:?}"
  );
}

#[test]
fn subsequent_var_r4_from_enum_overload_returns() {
  // Conformance: enumAssignabilityInInheritance — repeated `var r4` from
  // overload returns E then Object must emit TS2403.
  let src = r#"
enum E { A }
declare function foo2(x: string): string;
declare function foo2(x: E): E;
var r4 = foo2(E.A);
declare function foo16(x: Object): Object;
declare function foo16(x: E): E;
var r4 = foo16(E.A);
declare function foo17(x: {}): {};
declare function foo17(x: E): E;
var r4 = foo16(E.A);
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2403: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2403")
    .collect();
  assert_eq!(
    ts2403.len(),
    2,
    "expected 2× TS2403 for Object≠E redeclarations, got {diags:?}"
  );
}
