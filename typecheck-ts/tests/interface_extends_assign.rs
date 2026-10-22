use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn incompatible_property_override_is_ts2430() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface Base {
  a: (x: number) => number;
}
interface Derived extends Base {
  a: (x: number) => string;
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.to_string())
    .collect();
  assert!(
    codes.iter().any(|c| c == "TS2430"),
    "expected TS2430, got {codes:?}"
  );
}

#[test]
fn compatible_void_return_override_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface Base {
  a: (x: number) => void;
}
interface Derived extends Base {
  a: (x: number) => number;
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2430"),
    "expected no TS2430 for void-return base, got {diags:?}"
  );
}

#[test]
fn generic_iface_non_generic_override_is_ts2430() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface A {
  a2: (x: number) => string[];
}
interface I2<T, U> extends A {
  a2: (x: T) => U[];
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.to_string())
    .collect();
  assert!(
    codes.iter().any(|c| c == "TS2430"),
    "expected TS2430 for I2<T,U> extends A, got {codes:?}"
  );
}

#[test]
fn i4e_style_generic_default_constraint_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string = ""; }
class Derived extends Base { bar: string = ""; }
class Derived2 extends Derived { baz: string = ""; }
interface A {
  a12: (x: Array<Base>, y: Array<Derived2>) => Array<Derived>;
}
interface I4E extends A {
  a12: <T extends Array<Derived2>>(x: Array<Base>, y: Array<Base>) => T;
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.to_string()).collect();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2430"),
    "expected no TS2430 for I4E-style, got {codes:?}"
  );
}
