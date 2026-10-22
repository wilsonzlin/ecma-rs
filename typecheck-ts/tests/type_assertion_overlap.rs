use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn null_asserted_to_class_is_ts2352() {
  let src = r#"
class Derived { bar: string }
var x = <Derived>null;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2352: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2352")
    .collect();
  assert_eq!(
    ts2352.len(),
    1,
    "expected TS2352 for <Derived>null, got {diags:?}"
  );
}

#[test]
fn interface_asserted_to_number_is_ts2352() {
  let src = r#"
interface I1 { p1: number }
var z: I1 = { p1: 10 };
var b = <number>z;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2352: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2352")
    .collect();
  assert_eq!(
    ts2352.len(),
    1,
    "expected TS2352 for <number>z, got {diags:?}"
  );
}

#[test]
fn assertion_through_unknown_ok() {
  let src = r#"
class Derived { bar: string }
var x = null as unknown as Derived;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2352"),
    "unknown bridge should suppress TS2352, got {diags:?}"
  );
}

#[test]
fn union_assertion_overlaps_via_literal_comparability() {
  // tsc `checkAssertionWorker` uses the *comparable* relation: a primitive is
  // comparable to a literal of its own kind, so asserting a union with a
  // literal constituent to the primitive is allowed
  // (`stringLiteralTypeAssertion01.ts`).
  let src = r#"
type S = "a" | "b";
type T = S[] | S;
var s: S;
var t: T;
var str: string;
t = s as T;
t = <T>s;
str = t as string;
str = <string>t;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2352"),
    "overlapping assertions must not emit TS2352, got {diags:?}"
  );
}

#[test]
fn incomparable_assertion_still_ts2352() {
  let src = r#"
var n: number = 0;
var s = <string>n;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  let ts2352: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2352")
    .collect();
  assert_eq!(
    ts2352.len(),
    1,
    "expected TS2352 for <string>n, got {diags:?}"
  );
}

#[test]
fn literal_to_same_kind_literal_is_not_ts2352() {
  // tsc `checkAssertionDeferred` widens the source to its base literal form
  // before the comparable check: `"foo" as "bar"` compares `"bar"` against
  // the widened `string` and is allowed (`stringLiteralsWithTypeAssertions01`).
  let src = r#"
let a = "foo" as "bar";
let b = "bar" as "foo";
let c = 1 as 2;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2352"),
    "literal-to-same-kind-literal assertions must not emit TS2352, got {diags:?}"
  );
}

#[test]
fn literal_union_to_other_literal_is_not_ts2352() {
  // `fooOrBar as "baz"` / `"baz" as typeof fooOrBar`: the widened source is
  // `string`, comparable to any string literal.
  let src = r#"
let fooOrBar: "foo" | "bar" = "foo";
let e = fooOrBar as "baz";
let f = "baz" as typeof fooOrBar;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let diags = Program::new(host, vec![file]).check();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2352"),
    "widened literal-union assertions must not emit TS2352, got {diags:?}"
  );
}
