//! Interface-extends checks for generic base members (tsc
//! `callSignatureAssignabilityInInheritance6.ts`): an interface type
//! parameter is nominal to its container and never unifies with a *method's*
//! type parameter — a concrete member mentioning the interface's `T` cannot
//! satisfy a generic base signature ("two different types with this name
//! exist", TS2430).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
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
fn interface_param_does_not_satisfy_method_generic() {
  // tsc: `interface I<T> extends A` is TS2430 — I's `T` (nominal to the
  // interface) is not the method's generic `T`.
  let src = r#"
interface A {
    a: <T>(x: T) => T[];
    a2: <T>(x: T) => string[];
}
interface I<T> extends A {
    a: (x: T) => T[];
}
interface I2<T> extends A {
    a2: (x: T) => string[];
}
"#;
  let diags = codes(CompilerOptions::default(), src);
  assert_eq!(diags.len(), 2, "expected two TS2430, got {diags:?}");
  assert!(diags.iter().all(|c| c == "TS2430"), "{diags:?}");
}

#[test]
fn generic_own_member_still_unifies() {
  // A generic own member with matching structure unifies with the generic
  // base signature (no TS2430).
  let src = r#"
interface A {
    a: <T>(x: T) => T[];
}
interface I2<T> extends A {
    a: <U>(x: U) => U[];
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn concrete_compatible_member_is_fine() {
  // A concrete member with no type-parameter mentions still instantiates the
  // generic base — `interface I extends A { a: (x: number) => number[] }`
  // is incompatible per tsc (for-all-T fails), but a *generic* base method
  // with a concrete compatible own member works.
  let src = r#"
interface A {
    a: <T>(x: T) => T[];
}
interface I extends A {
    a: <T>(x: T) => T[];
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn construct_signature_nominal_rule() {
  // Same nominal rule for *construct* signatures
  // (`constructSignatureAssignabilityInInheritance6.ts`): I's `T` cannot
  // satisfy the base's generic `new <T>` member (TS2430), while a generic own
  // construct signature unifies.
  let src = r#"
interface A {
    a: new <T>(x: T) => T[];
}
interface I<T> extends A {
    a: new (x: T) => T[];
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), ["TS2430"]);

  let src_ok = r#"
interface A {
    a: new <T>(x: T) => T[];
}
interface I2<T> extends A {
    a: new <U>(x: U) => U[];
}
"#;
  assert_eq!(
    codes(CompilerOptions::default(), src_ok),
    Vec::<String>::new()
  );
}
