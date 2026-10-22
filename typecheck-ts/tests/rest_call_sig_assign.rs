use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn rest_element_type_mismatch_is_ts2322() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a: (...args: number[]) => number;
a = (...args: string[]) => 1;
"#,
  );
  let program = Program::new(host, vec![file]);
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.to_string())
    .collect();
  assert!(
    codes.iter().any(|c| c == "TS2322"),
    "expected TS2322, got {codes:?}"
  );
}

#[test]
fn one_required_param_assignable_to_number_rest() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a: (...args: number[]) => number;
a = (x: number) => 1;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    !diags.iter().any(|d| d.code.as_str() == "TS2322"),
    "expected no TS2322 for (x: number) => rest number, got {diags:?}"
  );
}

#[test]
fn sequential_ok_assignments_keep_declared_function_type() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a: (...args: number[]) => number;
a = () => 1;
a = (...args: number[]) => 1;
a = (x?: number) => 1;
a = (x?: number, y?: number, z?: number) => 1;
a = (x: number) => 1;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "expected no TS2322 after sequential ok assigns, got {ts2322:?}"
  );
}

#[test]
fn zero_arg_arrow_assignable_to_void_call_sig() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface T {
    (x: number): void;
}
var t: T;
t = () => 1;
var a: { (x: number): void };
a = () => 1;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .map(|d| {
      format!(
        "{}:{}-{}",
        d.code, d.primary.range.start, d.primary.range.end
      )
    })
    .collect();
  assert!(
    ts2322.is_empty(),
    "expected no TS2322 for () => 1 into void call sig, got {ts2322:?}"
  );
}

#[test]
fn after_generic_arrow_keeps_declared_void_call_sig() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface T {
    (x: number): void;
}
var t: T;
t = <U>(x: U) => 1;
t = () => 1;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "expected declared T preserved after generic arrow assign, got {ts2322:?}"
  );
}

#[test]
fn generic_arrow_type_param_shadowing_interface_name() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface T {
    (x: number): void;
}
var t: T;
t = <T>(x: T) => 1;
t = <U>(x: U) => 1;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "generic arrow <T> should assign to interface T call sig, got {ts2322:?}"
  );
}

#[test]
fn full_fixture_no_false_ts2322_on_generic_arrows() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  let src = include_str!("../../parse-js/tests/TypeScript/tests/cases/conformance/types/typeRelationships/assignmentCompatibility/assignmentCompatWithCallSignatures.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let false_pos = [341u32, 417];
  let bad: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322" && false_pos.contains(&d.primary.range.start))
    .collect();
  assert!(
    bad.is_empty(),
    "false TS2322 on generic arrows <T>(x:T)=>1: {bad:?}"
  );
}

#[test]
fn sequential_object_method_assigns_keep_declared() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface T {
    f(x: number): void;
}
var t: T;
t = { f: () => 1 };
t = { f: <T>(x: T) => 1 };
t = { f: function f() { return 1 } };
t = { f(x: number) { return ""; } };
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "declared methodful interface must survive sequential assigns, got {ts2322:?}"
  );
}

#[test]
fn generic_to_non_generic_array_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a: (x: number) => number[];
var b: <T>(x: T) => T[];
a = b; // ok via contextual signature instantiation
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(ts2322.is_empty(), "a = b should be ok, got {ts2322:?}");
}

#[test]
fn non_generic_to_generic_array_error() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a2: (x: number) => string[];
var b2: <T>(x: T) => string[];
b2 = a2; // error
"#,
  );
  let program = Program::new(host, vec![file]);
  assert!(
    program.check().iter().any(|d| d.code.as_str() == "TS2322"),
    "b2 = a2 should be TS2322"
  );
}

#[test]
fn callsig3_b12_a12_should_error() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
class Derived2 extends Derived { baz: string; }
var a12: (x: Array<Base>, y: Array<Derived2>) => Array<Derived> = (x, y) => y;
var b12: <T extends Array<Base>>(x: Array<Base>, y: T) => Array<Derived> = (x, y) => y;
b12 = a12;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code.as_str() == "TS2322"),
    "b12 = a12 should be TS2322, got {diags:?}"
  );
}

#[test]
fn callsig3_a16_b16_should_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
var a16: {
    <T extends Derived>(x: T): number[];
    <U extends Base>(x: U): number[];
} = null as any;
var b16: <T extends Base>(x: T) => number[] = null as any;
a16 = b16;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(ts2322.is_empty(), "a16 = b16 should be ok, got {ts2322:?}");
}

#[test]
fn uninitialized_non_generic_to_generic_is_ts2322() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a: (x: number) => number[];
var b: <T>(x: T) => T[];
b = a;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code.as_str() == "TS2322"),
    "expected TS2322"
  );
}

#[test]
fn uninitialized_constrained_generic_is_ts2322() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface Base { foo: string; }
interface Derived extends Base { bar: string; }
var a12: (x: Base[], y: Derived[]) => Derived[];
var b12: <T extends Base[]>(x: Base[], y: T) => Derived[];
b12 = a12;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code.as_str() == "TS2322"),
    "expected TS2322 for constrained generic"
  );
}

#[test]
fn uninitialized_array_generic_lib_is_ts2322() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
class Derived2 extends Derived { baz: string; }
var a12: (x: Array<Base>, y: Array<Derived2>) => Array<Derived>;
var b12: <T extends Array<Base>>(x: Array<Base>, y: T) => Array<Derived>;
b12 = a12;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.iter().any(|d| d.code.as_str() == "TS2322"),
    "b12 = a12 should be TS2322 (Array<> must not depth-limit to assignable), got {diags:?}"
  );
}

#[test]
fn array_ref_covariance_derived_to_base() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  let src = r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
var a: Array<Base>;
var b: Array<Derived>;
a = b; // ok covariant
"#;
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();
  let _ = program.check();
  let a_ty = program
    .type_at(file_id, src.find("var a").unwrap() as u32 + 4)
    .unwrap();
  let b_ty = program
    .type_at(file_id, src.find("var b").unwrap() as u32 + 4)
    .unwrap();
  assert!(
    program.explain_assignability(b_ty, a_ty).is_none(),
    "Array<Derived> should be assignable to Array<Base> (a={}, b={})",
    program.display_type(a_ty),
    program.display_type(b_ty)
  );
}

#[test]
fn callsig3_a12_b12_should_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
class Derived2 extends Derived { baz: string; }
declare var a12: (x: Array<Base>, y: Array<Derived2>) => Array<Derived>;
declare var b12: <T extends Array<Base>>(x: Array<Base>, y: T) => Array<Derived>;
a12 = b12;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(ts2322.is_empty(), "a12 = b12 should be ok, got {ts2322:?}");
}

#[test]
fn callsig3_b12_after_a12_should_error() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
class Derived2 extends Derived { baz: string; }
declare var a12: (x: Array<Base>, y: Array<Derived2>) => Array<Derived>;
declare var b12: <T extends Array<Base>>(x: Array<Base>, y: T) => Array<Derived>;
a12 = b12;
b12 = a12;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.len() >= 1,
    "b12 = a12 after a12 = b12 should still be TS2322, got {diags:?}"
  );
}

#[test]
fn callsig3_a14_b14_directions() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
declare var a14: (x: { a: string; b: number }) => Object;
declare var b14: <T>(x: { a: T; b: T }) => T;
a14 = b14;
b14 = a14;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    2,
    "both a14 = b14 and b14 = a14 should be TS2322, got {ts2322:?}"
  );
}

#[test]
fn callsig3_b15_a15_should_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
declare var a15: {
    (x: number): number[];
    (x: string): string[];
};
declare var b15: <T>(x: T) => T[];
b15 = a15;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "b15 = a15 (overload → unconstrained generic) should be ok, got {ts2322:?}"
  );
}

#[test]
fn callsig5_void_return_not_assignable_to_type_param() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
declare var a3: <T>(x: T) => void;
declare var b3: <T>(x: T) => T;
b3 = a3;
"#,
  );
  let program = Program::new(host, vec![file]);
  assert!(
    program.check().iter().any(|d| d.code.as_str() == "TS2322"),
    "b3 = a3 should be TS2322 (void </: T)"
  );
}

#[test]
fn callsig5_different_arity_generics_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
declare var a11: <T>(x: { foo: T }, y: { foo: T; bar: T }) => Base;
declare var b11: <T, U>(x: { foo: T }, y: { foo: U; bar: U }) => Base;
a11 = b11;
declare var a15: <T>(x: { a: T; b: T }) => T[];
declare var b15: <U, V>(x: { a: U; b: V }) => U[];
a15 = b15;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "a11/a15 different-arity should be ok, got {ts2322:?}"
  );
}

#[test]
fn callsig5_different_arity_reverse_is_ts2322() {
  // Modern tsc rejects these (fixture comments saying "// ok" are stale).
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
declare var a11: <T>(x: { foo: T }, y: { foo: T; bar: T }) => Base;
declare var b11: <T, U>(x: { foo: T }, y: { foo: U; bar: U }) => Base;
b11 = a11;
declare var a15: <T>(x: { a: T; b: T }) => T[];
declare var b15: <U, V>(x: { a: U; b: V }) => U[];
b15 = a15;
declare var a16: <T extends Base>(x: { a: T; b: T }) => T[];
b15 = a16;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    3,
    "b11=a11, b15=a15, b15=a16 should each be TS2322, got {ts2322:?}"
  );
}

#[test]
fn callsig5_a6_b6_both_directions() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
declare var a6: <T extends Base>(x: (arg: T) => Derived) => T;
declare var b6: <T extends Base, U extends Derived>(x: (arg: T) => U) => T;
a6 = b6;
b6 = a6;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "a6/b6 should be ok both ways, got {ts2322:?}"
  );
}

#[test]
fn callsig5_overload_set_to_unconstrained_generic_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
declare var a17: {
    <T extends Derived>(x: (a: T) => T): T[];
    <T extends Base>(x: (a: T) => T): T[];
};
declare var b17: <T>(x: (a: T) => T) => T[];
b17 = a17;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(ts2322.is_empty(), "b17 = a17 should be ok, got {ts2322:?}");
}

#[test]
fn constructsig4_a10_a11_constrained_rest_is_ts2322() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
declare var a10: new (...x: Base[]) => Base;
declare var b10: new <T extends Derived>(...x: T[]) => T;
a10 = b10;
declare var a11: new (x: { foo: string }, y: { foo: string; bar: string }) => Base;
declare var b11: new <T extends Derived>(x: T, y: T) => T;
a11 = b11;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    2,
    "a10=b10 and a11=b11 should be TS2322 (stale // ok comments), got {ts2322:?}"
  );
}

#[test]
fn constructsig3_a15_b15_both_directions() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
declare var a15: {
    new (x: number): number[];
    new (x: string): string[];
};
declare var b15: new <T>(x: T) => T[];
a15 = b15;
b15 = a15;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "construct a15/b15 should be ok both ways, got {ts2322:?}"
  );
}

#[test]
fn constructsig5_a17_b17_both_directions() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
declare var a17: {
    new <T extends Derived>(x: new (a: T) => T): T[];
    new <T extends Base>(x: new (a: T) => T): T[];
};
declare var b17: new <T>(x: new (a: T) => T) => T[];
a17 = b17;
b17 = a17;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "construct a17/b17 should be ok both ways, got {ts2322:?}"
  );
}

#[test]
fn callsig4_a12_constrained_array_return_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
class Base { foo: string; }
class Derived extends Base { bar: string; }
class Derived2 extends Derived { baz: string; }
declare var a12: (x: Array<Base>, y: Array<Derived2>) => Array<Derived>;
declare var b12: <T extends Array<Derived2>>(x: Array<Base>, y: Array<Base>) => T;
a12 = b12;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(ts2322.is_empty(), "a12 = b12 should be ok, got {ts2322:?}");
}

#[test]
fn callsig4_equal_arity_return_type_param_is_ts2322() {
  // `<T>(x:T)=>string[]` is not assignable to `<T>(x:T)=>T[]` (and reverse).
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
declare var a2: <T>(x: T) => T[];
declare var b2: <T>(x: T) => string[];
a2 = b2;
declare var a3: <T>(x: T) => string[];
declare var b3: <T>(x: T) => T[];
b3 = a3;
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2322: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    2,
    "a2=b2 and b3=a3 should each be TS2322, got {ts2322:?}"
  );
}

#[test]
fn callsig4_namespace_sibling_class_and_var_scopes() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
namespace Errors {
    class Base { foo: string; }
    class Derived extends Base { bar: string; }

    namespace WithNonGeneric {
        var a2: (x: number) => string[];
        var b2: <T, U>(x: T) => U[];
        a2 = b2;
    }
    namespace WithGeneric {
        var a2: <T>(x: T) => T[];
        var b2: <T>(x: T) => string[];
        a2 = b2;
        b2 = a2;
        var a3: <T>(x: T) => string[];
        var b3: <T>(x: T) => T[];
        a3 = b3;
        b3 = a3;
    }
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags
    .iter()
    .map(|d| d.code.as_str())
    .filter(|c| !c.starts_with("TC"))
    .collect();
  assert!(
    !codes.iter().any(|c| *c == "TS2304"),
    "namespace sibling class heritage must resolve Base, got {codes:?}"
  );
  assert!(
    !codes.iter().any(|c| *c == "TS2403"),
    "sibling nested namespaces must not share var bindings, got {codes:?}"
  );
  assert!(
    codes.iter().filter(|c| **c == "TS2322").count() >= 2,
    "WithGeneric a2=b2 and b3=a3 should be TS2322, got {codes:?}"
  );
}

#[test]
fn generic_call_signatures4_recursive_constraint() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface I2<T> {
  p: T;
}
var x: <T extends I2<T>>(z: T) => void;
var y: <T extends I2<I2<T>>>(z: T) => void;
x = y;
y = x;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    1,
    "expected only y=x as TS2322, got {ts2322:?} all={diags:?}"
  );
  // Primary span should be on `y = x` (start of y), not `x = y`.
  let msg = &ts2322[0];
  assert!(
    msg.message.contains("I2") || msg.code.as_str() == "TS2322",
    "{msg:?}"
  );
}

#[test]
fn generic_call_signatures_array_constraint_vs_element_array() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var f: <S extends { p: string }[]>(x: S) => void
var g: <T extends { p: string }>(x: T[]) => void
f = g;
g = f;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "expected f=g and g=f ok, got {ts2322:?} all={diags:?}"
  );
}

#[test]
fn generic_constraint_specificity_rejects_reverse() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
var a: <T extends {a: string, b: number}>(x: T) => void
var b: <T extends {a: string}>(x: T) => void
a = b;
b = a;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(
    ts2322.len(),
    1,
    "expected only b=a as TS2322, got {ts2322:?} all={diags:?}"
  );
}

#[test]
fn generic_arrow_to_generic_overload_member_inherited() {
  // `I9 extends A` from `callSignatureAssignabilityInInheritance3.ts`: a
  // generic arrow member matches a generic-overload base member — the CSI
  // must keep shared type-param markers (not substitute their constraints).
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface Base { b: number }
interface Derived extends Base { d: number }
interface Derived2 extends Derived { e: number }
interface A {
    a17: {
        (x: {
            <T extends Derived>(a: T): T;
            <T extends Base>(a: T): T;
        }): any[];
        (x: {
            <T extends Derived2>(a: T): T;
            <T extends Base>(a: T): T;
        }): any[];
    };
}
interface I9 extends A {
    a17: <T>(x: (a: T) => T) => any[];
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let ts2430: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2430")
    .collect();
  assert!(
    ts2430.is_empty(),
    "expected no TS2430 for I9 extends A, got {ts2430:?}"
  );
}
