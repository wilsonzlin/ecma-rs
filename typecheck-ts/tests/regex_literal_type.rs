//! Regex literals type as the global `RegExp` interface (tsc), never `string`
//! or `unknown` (`controlFlowForInStatement.ts`: `x = /a/`).

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
fn regex_literal_assigns_to_regexp_annotation() {
  let src = r#"let r: RegExp = /a/;"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn regex_literal_assigns_to_union_with_regexp() {
  let src = r#"let x: string | number | boolean | RegExp | Function;
x = /a/;"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn regex_literal_exposes_regexp_members() {
  let src = r#"const ok: boolean = /a/.test("a");
const src2: string = /a/.source;"#;
  assert_eq!(codes(src), Vec::<String>::new());
}
