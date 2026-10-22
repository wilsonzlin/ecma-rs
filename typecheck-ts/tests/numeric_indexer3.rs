use typecheck_ts::{FileKey, MemoryHost, Program};

fn ts2322_starts(src: &str) -> Vec<u32> {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  Program::new(host, vec![file])
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .map(|d| d.primary.range.start)
    .collect()
}

#[test]
fn numeric_indexer3_non_generic_order_independent() {
  let src = r#"
interface Base { foo: string; }
interface Derived extends Base { bar: string; }
interface Derived2 extends Derived { baz: string; }
class A {
  [x: number]: Derived;
}
declare var a: A;
declare var b: { [x: number]: Base; };
declare var b2: { [x: number]: Derived2; };
a = b; // error
b = a; // ok
a = b2; // ok
b2 = a; // error
"#;
  let starts = ts2322_starts(src);
  for site in ["a = b; // error", "b2 = a; // error"] {
    let at = src.find(site).unwrap() as u32;
    assert!(
      starts.iter().any(|&s| s >= at && s < at + 6),
      "{site} should error, starts={starts:?}"
    );
  }
  for site in ["b = a; // ok", "a = b2; // ok"] {
    let at = src.find(site).unwrap() as u32;
    assert!(
      !starts.iter().any(|&s| s >= at && s < at + 6),
      "{site} should be ok, starts={starts:?}"
    );
  }
}

#[test]
fn numeric_indexer3_generic_without_outer_shadow() {
  let src = r#"
interface Derived { bar: string; }
class A<T extends Derived> {
  [x: number]: T;
}
function foo<T extends Derived>() {
  declare var a: A<T>;
  declare var b: { [x: number]: Derived; };
  declare var b2: { [x: number]: T; };
  a = b; // error
  b = a; // ok
  a = b2; // ok
  b2 = a; // ok
}
"#;
  let starts = ts2322_starts(src);
  let err = src.find("a = b; // error").unwrap() as u32;
  assert!(
    starts.iter().any(|&s| s >= err && s < err + 5),
    "a = b should error, starts={starts:?}"
  );
  for site in ["b = a; // ok", "a = b2; // ok", "b2 = a; // ok"] {
    let at = src.find(site).unwrap() as u32;
    assert!(
      !starts.iter().any(|&s| s >= at && s < at + 5),
      "{site} should be ok, starts={starts:?}"
    );
  }
}

#[test]
fn numeric_indexer3_generic_shadows_outer_class_a() {
  // Upstream fixture shape: outer `class A` + `namespace Generics { class A<T> }`.
  let src = r#"
interface Derived { bar: string; }
class A {
  [x: number]: Derived;
}
namespace Generics {
  class A<T extends Derived> {
    [x: number]: T;
  }
  function foo<T extends Derived>() {
    declare var a: A<T>;
    declare var b: { [x: number]: Derived; };
    declare var b2: { [x: number]: T; };
    a = b; // error
    b = a; // ok
    a = b2; // ok
    b2 = a; // ok
  }
}
"#;
  let starts = ts2322_starts(src);
  let err = src.find("a = b; // error").unwrap() as u32;
  assert!(
    starts.iter().any(|&s| s >= err && s < err + 5),
    "namespace-local A<T>: a = b should error, starts={starts:?}"
  );
  for site in ["b = a; // ok", "a = b2; // ok", "b2 = a; // ok"] {
    let at = src.find(site).unwrap() as u32;
    assert!(
      !starts.iter().any(|&s| s >= at && s < at + 5),
      "{site} should be ok, starts={starts:?}"
    );
  }
}
