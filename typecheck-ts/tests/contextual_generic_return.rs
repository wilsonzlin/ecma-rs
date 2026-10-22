//! Contextual lambda returns against generic call parameters are inference
//! targets, not declared ones: tsc defers the assignability check until the
//! call instantiates the type arguments. Regression for false TS2322s after
//! free type params became nominal assignment targets
//! (`contextual_callbacks` / `reference_lib` difftsc fixtures).

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
fn contextual_arrow_return_infers_type_argument() {
  let src = r#"
function map<T, U>(items: T[], fn: (value: T, index: number) => U): U[] {
  return [] as any;
}
const doubled = map([1, 2, 3], (n, idx) => {
  return n + idx;
});
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn expression_bodied_arrow_return_infers_type_argument() {
  let src = r#"
declare function map<T, U>(items: T[], fn: (value: T, index: number) => U): U[];
const strings = map([1, 2, 3], (n) => n.toFixed());
declare function h<T>(cb: (x: T) => T): void;
h((x) => 5);
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn explicit_type_args_recheck_return() {
  // With the signature instantiated (`U = string`), the return is checked
  // against a concrete type and tsc reports on the return expression.
  let src = r#"
declare function map<T, U>(items: T[], fn: (value: T, index: number) => U): U[];
const r = map<number, string>([1], (n, i) => n + i);
declare function h<T>(cb: (x: T) => T): void;
h<string>((x) => 5);
"#;
  let c = codes(src);
  assert!(
    c.iter().filter(|x| *x == "TS2322").count() == 2,
    "expected two TS2322 (one per instantiated return): {c:?}"
  );
}

#[test]
fn declared_type_param_return_stays_nominal() {
  // The function's own declared return parameter is a nominal target
  // (unchanged): concrete types do not flow into it.
  let src = r#"
function f<T>(): T {
  return 5;
}
"#;
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "expected TS2322 for `return 5` in `<T>(): T`: {c:?}"
  );
}
