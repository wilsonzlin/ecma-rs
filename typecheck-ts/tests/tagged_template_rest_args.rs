//! Tagged-template rest callback params annotated with the lib `Array<X>`
//! interface form: substitutions must be contextually typed by the *element*
//! type (`taggedTemplatesWithTypeArguments1.ts`).

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
fn rest_array_interface_callbacks_type_substitutions() {
  let src = r#"
declare function f<T>(strs: TemplateStringsArray, ...callbacks: Array<(x: T) => any>): void;
interface Stuff { x: number; y: string; z: boolean }
export const a = f<Stuff> `
    hello
    ${stuff => stuff.x}
    brave
    ${stuff => stuff.y}
    world
    ${stuff => stuff.z}
`;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn rest_array_interface_wrong_substitution_still_errors() {
  // tsc emits TS2322 on the arrow's return expression when the substitution's
  // return type mismatches the callback's.
  let src = r#"
declare function f<T>(strs: TemplateStringsArray, ...callbacks: Array<(x: T) => number>): void;
interface Stuff { x: string }
export const a = f<Stuff> `
    hello
    ${stuff => stuff.x}
`;
"#;
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "expected TS2322 for string substitution vs number callback: {c:?}"
  );
}
