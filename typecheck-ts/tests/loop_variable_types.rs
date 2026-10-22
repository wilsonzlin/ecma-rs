//! Loop-variable typing (tsc parity): `for…in` variables are always `string`;
//! `for…of` variables take the iterated element type. Regression for the AST
//! binding path poisoning downstream assignment checks with `unknown`
//! (`controlFlowForInStatement.ts`, `ES5For-of34.ts`).

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
fn for_in_variable_is_string() {
  let src = r#"
let x: string | number | boolean | RegExp | Function;
let obj: any;
x = /a/;
for (let y in obj) {
  x = y;
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn for_of_variable_takes_element_type() {
  // tsc: the loop variable is the element type; assigning it to an
  // incompatible target is a real error (kept), not suppressed.
  let ok = r#"
let out: string = "";
for (const s of ["a", "b"]) {
  out = s;
}
"#;
  assert_eq!(codes(ok), Vec::<String>::new());

  let bad = r#"
declare function foo(): { x: number };
for (foo().x of ["a", "b", "c"]) {
  var p = foo().x;
}
"#;
  let c = codes(bad);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "expected TS2322 assigning string elements to number target: {c:?}"
  );
}

#[test]
fn for_of_over_any_iterates_any() {
  let src = r#"
let x: string | number;
declare const obj: any;
for (const y of obj) {
  x = y as any;
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}
