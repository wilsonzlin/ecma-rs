//! Mapped-type instantiation per tsc (`instantiateMappedType` /
//! `instantiateConstituent`), covering the `mappedTypes4.ts` failures:
//!
//! - **Homomorphic collapse**: for `{[P in keyof T]: X}`, instantiating `T`
//!   with a primitive yields the primitive (`DeepReadonly<number>` is
//!   `number`); unions distribute with primitives passing through
//!   (`DR<A | undefined>` is `DR<A> | undefined`). Instantiables (free type
//!   params, indexed access, conditionals) are *not* collapsed.
//! - **Indexed access over intersections**: `(Z & {})["a"]` is `number`
//!   (mapped types over `keyof (T & {})`, e.g. `Clone<Z>`).
//! - **Union source to a naked type parameter**: `boxify(x)` with
//!   `x: A | B | undefined` infers `T = A | B | undefined` (tsc keeps the
//!   union as a single candidate; it does not distribute + first-win).
//! - **TS2403 identity**: `var x1: DeepReadonly<Foo>; var x1: DeepReadonlyFoo;`
//!   does not fire (structurally identical after evaluation).

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
fn union_source_infers_whole_union_for_naked_type_param() {
  let src = r#"
type Box<T> = {};
type Boxified<T> = { [P in keyof T]: Box<T[P]>; };
declare function boxify<T>(obj: T): Boxified<T>;
type A = { a: string };
type B = { b: string };
type C = { c: string };
declare const x: A | B | C | undefined;
const r = boxify(x);
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn homomorphic_mapped_over_primitive_collapses() {
  let src = r#"
type DR<T> = { readonly [P in keyof T]: DR<T[P]> };
declare const d: DR<number>;
let n: number = d;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn recursive_homomorphic_mapped_evaluates_deeply() {
  let src = r#"
type Foo = { x: number; y: { a: string, b: number }; z: boolean; };
type DR<T> = { readonly [P in keyof T]: DR<T[P]> };
declare const d: DR<Foo>;
let n: number = d.x;
let s: string = d.y.a;
let b: boolean = d.z;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn homomorphic_union_distributes_with_primitive_passthrough() {
  let src = r#"
type A = { a: string };
type DR<T> = { readonly [P in keyof T]: DR<T[P]> };
declare const d: DR<A | undefined>;
let u: undefined | { readonly a: string } = d;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn keyof_intersection_mapped_type_evaluates() {
  // `Clone<Z>` per `mappedTypes4` (`keyof (T & {})`).
  let src = r#"
type Z = { a: number };
type Clone<T> = { [P in keyof (T & {})]: (T & {})[P] };
declare const d: Clone<Z>;
let n: number = d.a;
var z1: Z;
var z1: Clone<Z>;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn mapped_identity_suppresses_ts2403() {
  let src = r#"
type Foo = { x: number; y: { a: string, b: number }; z: boolean; };
type DeepReadonly<T> = { readonly [P in keyof T]: DeepReadonly<T[P]>; };
type DeepReadonlyFoo = { readonly x: number; readonly y: { readonly a: string, readonly b: number }; readonly z: boolean; };
var x1: DeepReadonly<Foo>;
var x1: DeepReadonlyFoo;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn empty_object_assertion_to_generic_mapped_type_is_allowed() {
  let src = r#"
type Box<T> = {};
type Boxified<T> = { [P in keyof T]: Box<T[P]>; };
function boxify<T>(obj: T): Boxified<T> {
    let result = {} as Boxified<T>;
    return result;
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}
