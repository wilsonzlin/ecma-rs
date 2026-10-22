//! Missing type arguments are filled with the declared defaults
//! (`Iterator<Foo>` ≡ `Iterator<Foo, any, any>` — tsc
//! `getTypeArgumentsWithDefaults`), and unannotated type parameters on the
//! same generic symbol compare with *measured* variance (output positions
//! covariant, parameter positions contravariant; tsc
//! `getStructuralVariancesOfTypeParameters`) rather than blindly invariantly.
//! Together these make `Generator<Bar>` assignable to `Iterable<Foo>`
//! (`generatorTypeCheck25.ts` territory).

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
fn partial_type_args_fill_defaults() {
  // `Iterator<Foo>` must equal `Iterator<Foo, any, any>`.
  let src = "class Foo { x: number }\ndeclare const g: Generator<Foo, void, unknown>;\nconst x: { [Symbol.iterator](): Iterator<Foo> } = g;\nconst y: { [Symbol.iterator](): Iterator<Foo, any, any> } = g;";
  assert!(codes(src).is_empty());
}

#[test]
fn unannotated_generic_interface_is_covariant_in_output_positions() {
  // Box<Bar> is assignable to Box<Foo> when Bar extends Foo (property output
  // position, measured covariant).
  let src = "class Foo { x: number }\nclass Bar extends Foo { y: string }\ninterface Box<T> { value: T }\ndeclare const r: Box<Bar>;\nconst r2: Box<Foo> = r;";
  assert!(codes(src).is_empty());
}

#[test]
fn generic_class_with_param_positions_stays_invariant() {
  // `C<T>` with a method parameter of type `T` is covariant in T per tsc
  // (method parameters are bivariant), so C<Bar> → C<Foo> is clean but
  // C<Foo> → C<Bar> (base to derived) still fails.
  let src = "class Foo { x: number }\nclass Bar extends Foo { y: string }\nclass C<T> { m(x: T): T { return x; } }\ndeclare const a: C<Foo>;\nconst b: C<Bar> = a;";
  assert_eq!(codes(src), ["TS2322"]);
  let reverse = "class Foo { x: number }\nclass Bar extends Foo { y: string }\nclass C<T> { m(x: T): T { return x; } }\ndeclare const a: C<Bar>;\nconst b: C<Foo> = a;";
  assert!(codes(reverse).is_empty());
}

#[test]
fn private_field_keeps_generic_class_invariant() {
  // A `#foo: T` field makes `C<number>` and `C<string>` unrelated in both
  // directions (`privateNamesInGenericClasses.ts`).
  let src = "class C<T> {\n  #foo: T;\n  #method(): T { return this.#foo; }\n  bar(x: C<T>) { return x.#foo; }\n}\ndeclare let a: C<number>;\ndeclare let b: C<string>;\na = b;\nb = a;";
  assert_eq!(codes(src), ["TS2322", "TS2322"]);
}

#[test]
fn generator_assignable_to_iterable_of_base() {
  // Generator<Bar, void, unknown> → Iterable<Foo> (yield covariance through
  // IteratorObject → Iterator → Iterable).
  let src = "class Foo { x: number }\nclass Bar extends Foo { y: string }\ndeclare const gen: Generator<Bar, void, unknown>;\nconst it: Iterable<Foo> = gen;";
  assert!(codes(src).is_empty());
}
