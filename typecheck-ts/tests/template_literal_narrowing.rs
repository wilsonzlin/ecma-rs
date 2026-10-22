//! No-substitution template literals (`` `string` ``) are string literals for
//! control-flow narrowing, matching tsc (`controlFlowWithTemplateLiterals.ts`):
//! `typeof x === `tag`` narrows like `typeof x === "tag"`, and `` `k` in obj ``
//! narrows like `'k' in obj`.

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
fn typeof_with_template_tag_narrows() {
  // Exact shape of the upstream case: both checks must be clean.
  let src = r#"declare const envVar: string | undefined;
if (typeof envVar === `string`) {
  envVar.slice(0)
}

declare const obj: {test: string} | {}
if (`test` in obj) {
  obj.test.slice(0)
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn template_tag_parity_with_plain_string_tag() {
  // Template tags must behave exactly like plain string tags (the union
  // `typeof u === 'undefined'` assignment shape has a pre-existing AST-pass
  // narrowing gap — identical for plain and template tags).
  let template = "declare const u: string | number | undefined;\nif (typeof u === `undefined`) {\n  const v: undefined = u;\n}\n";
  let plain = "declare const u: string | number | undefined;\nif (typeof u === 'undefined') {\n  const v: undefined = u;\n}\n";
  assert_eq!(codes(template), codes(plain));
}

#[test]
fn substitution_template_is_not_a_literal_tag() {
  // `` `${x}` `` is not a literal tag: no narrowing, but also no diagnostics
  // for a plain use.
  let src = r#"declare const u: string | number;
declare const tag: string;
if (typeof u === `${tag}`) {
  u;
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}
