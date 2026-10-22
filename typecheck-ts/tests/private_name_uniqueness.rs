//! TS2300 / TS2804 — private-identifier uniqueness within a class body.
//! Also covers cross-class private branding (assignability / TS18013).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, u32, u32)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| {
      (
        d.code.as_str().to_string(),
        d.primary.range.start,
        d.primary.range.end,
      )
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  diags(opts, src).into_iter().map(|(c, _, _)| c).collect()
}

fn opts() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts.strict_property_initialization = false;
  opts
}

#[test]
fn static_and_instance_same_private_name_is_ts2804() {
  // Mirrors conformance `privateNamesUnique-3.ts` (first class).
  let src = r#"
class A {
  #foo = 1;
  static #foo = true;
}
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS2804").count(), 1, "{c:?}");
}

#[test]
fn duplicate_instance_private_field_is_ts2300() {
  let src = r#"
class A {
  #foo = "a";
  #foo = "b";
}
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2300"),
    "expected TS2300 for duplicate field: {c:?}"
  );
}

#[test]
fn field_then_method_private_is_ts2300_on_both() {
  let src = r#"
class A {
  #foo = "a";
  #foo() {}
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2300").count(),
    2,
    "binder dual-report for field+method: {c:?}"
  );
}

#[test]
fn getter_setter_same_private_name_ok() {
  let src = r#"
class A {
  get #foo() { return ""; }
  set #foo(v: string) {}
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter().any(|x| x == "TS2300" || x == "TS2804"),
    "getter+setter must be allowed: {c:?}"
  );
}

#[test]
fn cross_class_private_assignability_is_ts2322() {
  // Mirrors conformance `privateNamesUnique-1.ts`.
  // Same `#foo` description on both classes → private-brand failure (TS2322),
  // not "missing property" (TS2741).
  let src = r#"
class A {
  #foo: number;
}
class B {
  #foo: number;
}
const b: A = new B();
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "distinct class privates must not assign: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2741"),
    "same-name cross-class private is TS2322, not TS2741: {c:?}"
  );
}

#[test]
fn missing_private_on_unrelated_type_is_ts2741() {
  // Mirrors conformance `privateNamesUnique-4.ts`.
  let src = r#"
class A1 { }
interface A2 extends A1 { }
declare const a: A2;
class C { #something: number }
const c: C = a;
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2741"),
    "absent required private must be TS2741: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2322"),
    "must not fall back to generic TS2322: {c:?}"
  );
}

#[test]
fn missing_required_public_property_is_ts2741() {
  let src = r#"
const x: { a: number } = {};
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2741"),
    "single missing required prop: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2322"),
    "prefer TS2741 over TS2322: {c:?}"
  );
}

#[test]
fn multiple_missing_required_properties_are_ts2739() {
  let src = r#"
const x: { a: number; b: string } = {};
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2739"),
    "multiple missing required props: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2322" || x == "TS2741"),
    "prefer TS2739 over TS2322/TS2741: {c:?}"
  );
}

#[test]
fn property_type_mismatch_stays_ts2322() {
  let src = r#"
const x: { a: number } = { a: "nope" };
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "present-but-wrong-type stays TS2322: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2741" || x == "TS2739"),
    "type mismatch is not a missing-prop code: {c:?}"
  );
}

#[test]
fn static_private_accessed_as_instance_is_ts2339() {
  // Second half of `privateNamesUnique-3.ts`.
  let src = r#"
class B {
  static #foo = true;
  test(x: B) {
    x.#foo;
  }
}
"#;
  let c = codes(opts(), src);
  assert!(
    c.iter().any(|x| x == "TS2339"),
    "static #foo is not an instance property: {c:?}"
  );
}

#[test]
fn duplicate_private_method_implementations_are_ts2393() {
  // `A_Method_Method` / `A_StaticMethod_StaticMethod` in privateNameDuplicateField.
  let src = r#"
class A {
  #foo() {}
  #foo() {}
}
class B {
  static #foo() {}
  static #foo() {}
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2393").count(),
    4,
    "both impls on each class: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2300"),
    "method/method is TS2393, not TS2300: {c:?}"
  );
}

#[test]
fn method_then_field_private_is_ts2300_and_ts2717() {
  // `A_Method_Field` / `A_StaticMethod_StaticField` in privateNameDuplicateField.
  let src = r#"
class A {
  #foo() {}
  #foo = "foo";
}
class B {
  static #foo() {}
  static #foo = "foo";
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2300").count(),
    2,
    "one TS2300 per class on the field: {c:?}"
  );
  assert_eq!(
    c.iter().filter(|x| *x == "TS2717").count(),
    2,
    "subsequent field type mismatch: {c:?}"
  );
}

#[test]
fn public_duplicate_method_implementations_are_ts2393() {
  let src = r#"
class A {
  foo() {}
  foo() {}
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2393").count(),
    2,
    "public method dual-impl: {c:?}"
  );
}

#[test]
fn method_overload_signature_plus_one_impl_ok() {
  let src = r#"
class A {
  foo(): void;
  foo() {}
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter().any(|x| x == "TS2393"),
    "single implementation with overload signature: {c:?}"
  );
}

#[test]
fn cross_file_import_type_private_access_is_ts18013() {
  // Mirrors conformance `privateNamesUnique-2.ts`: `other: import("./b").Foo`
  // then `other.#x` inside A's class must be TS18013 (distinct private brand).
  let mut host = MemoryHost::with_options(opts());
  let a = FileKey::new("a.ts");
  let b = FileKey::new("b.ts");
  host.insert(
    a.clone(),
    r#"
export class Foo {
  #x;
  copy(other: import("./b").Foo) {
    other.#x;
  }
}
"#,
  );
  host.insert(
    b.clone(),
    r#"
export class Foo {
  #x;
}
"#,
  );
  host.link(a.clone(), "./b", b.clone());
  let program = Program::new(host, vec![a, b]);
  let diags: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  assert_eq!(
    diags.iter().filter(|x| *x == "TS18013").count(),
    1,
    "expected TS18013 for other.#x via import(): {diags:?}"
  );
  assert!(
    !diags.iter().any(|x| x == "TS2339"),
    "must not fall back to TS2339 when private exists on import type: {diags:?}"
  );
}

#[test]
fn cross_file_imported_plain_class_is_constructable() {
  let mut host = MemoryHost::with_options(opts());
  let a = FileKey::new("a.ts");
  let main = FileKey::new("main.ts");
  host.insert(a.clone(), r#"export class Foo { x: number = 1; }"#);
  host.insert(
    main.clone(),
    r#"
import { Foo } from "./a";
const a = new Foo();
"#,
  );
  host.link(main.clone(), "./a", a.clone());
  let program = Program::new(host, vec![main, a]);
  let diags: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  assert!(
    !diags.iter().any(|x| x == "TC2000"),
    "plain imported class must be constructable: {diags:?}"
  );
}

#[test]
fn cross_file_imported_class_with_private_is_constructable() {
  // main.ts half of privateNamesUnique-2: `new A()` / `new B()` must not be TC2000.
  let mut host = MemoryHost::with_options(opts());
  let a = FileKey::new("a.ts");
  let b = FileKey::new("b.ts");
  let main = FileKey::new("main.ts");
  host.insert(
    a.clone(),
    r#"
export class Foo {
  #x;
  copy(other: import("./b").Foo) {
    other.#x;
  }
}
"#,
  );
  host.insert(
    b.clone(),
    r#"
export class Foo {
  #x;
}
"#,
  );
  host.insert(
    main.clone(),
    r#"
import { Foo as A } from "./a";
import { Foo as B } from "./b";
const a = new A();
const b = new B();
a.copy(b);
"#,
  );
  host.link(a.clone(), "./b", b.clone());
  host.link(main.clone(), "./a", a.clone());
  host.link(main.clone(), "./b", b.clone());
  let program = Program::new(host, vec![main, a, b]);
  let diags: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| format!("{}:{}", d.code.as_str(), d.message))
    .collect();
  assert!(
    !diags.iter().any(|x| x.starts_with("TC2000")),
    "imported class with private must be constructable: {diags:?}"
  );
}
