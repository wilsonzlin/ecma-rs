//! TS7008 — unannotated private fields under `--noImplicitAny`.
//! Mirrors conformance `privateNameAmbientNoImplicitAny.ts`.

use typecheck_ts::codes;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn ambient_private_field_skips_ts7008_concrete_emits() {
  let src = r#"
declare class A {
    #prop;
}
class B {
    #prop;
}
"#;
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    ..Default::default()
  });
  let key = FileKey::new("t.ts");
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();

  let member_any: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::MEMBER_IMPLICIT_ANY.as_str())
    .collect();
  assert_eq!(
    member_any.len(),
    1,
    "expected one TS7008 on concrete B.#prop, got {diagnostics:?}"
  );
  assert!(
    member_any[0].message.contains("Member '#prop'"),
    "message: {:?}",
    member_any[0].message
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::IMPLICIT_ANY.as_str()),
    "must not use TC3000 for class fields: {diagnostics:?}"
  );

  // Span is the name `#prop` on class B (not the ambient declare class).
  let b_prop = src.rfind("#prop").expect("#prop") as u32;
  assert_eq!(
    member_any[0].primary.range.start, b_prop,
    "span start: {:?}",
    member_any[0].primary.range
  );
  assert_eq!(
    member_any[0].primary.range.end,
    b_prop + 5,
    "span end: {:?}",
    member_any[0].primary.range
  );
}
