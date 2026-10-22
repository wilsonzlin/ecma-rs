//! TS7022 — circular private / computed field initializers under `--noImplicitAny`.
//! Mirrors conformance `privateNameCircularReference.ts` +
//! `privateNameAndIndexSignature.ts` (circularity half).

use typecheck_ts::codes;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn check(src: &str) -> Vec<typecheck_ts::Diagnostic> {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    strict_null_checks: true,
    ..Default::default()
  });
  let key = FileKey::new("t.ts");
  host.insert(key.clone(), src);
  Program::new(host, vec![key]).check()
}

#[test]
fn computed_self_ref_initializer_emits_ts7022_not_ts7008() {
  let src = r##"
class A {
    [k: string]: any;
    #foo = 3;
    ["#bar"] = this["#bar"];
}
"##;
  let diagnostics = check(src);
  let circ: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::CIRCULAR_INITIALIZER_IMPLICIT_ANY.as_str())
    .collect();
  assert_eq!(
    circ.len(),
    1,
    "expected one TS7022 on [\"#bar\"], got {diagnostics:?}"
  );
  assert!(
    circ[0].message.contains("[\"#bar\"]"),
    "message should use computed name display: {:?}",
    circ[0].message
  );
  let name_start = src.find("[\"#bar\"]").expect("computed key") as u32;
  assert_eq!(circ[0].primary.range.start, name_start);
  assert_eq!(circ[0].primary.range.end, name_start + 8);
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::MEMBER_IMPLICIT_ANY.as_str()),
    "must not emit TS7008 when TS7022 applies: {diagnostics:?}"
  );
}

#[test]
fn mutual_private_field_cycle_emits_ts7022_and_ts2729() {
  let src = r##"
class A {
    #foo = this.#bar;
    #bar = this.#foo;
    ["#baz"] = this["#baz"];
}
"##;
  let diagnostics = check(src);
  let circ: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::CIRCULAR_INITIALIZER_IMPLICIT_ANY.as_str())
    .collect();
  assert!(
    circ.len() >= 3,
    "expected TS7022 on #foo, #bar, [\"#baz\"], got {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected TS2729 for #bar use-before-init: {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::MEMBER_IMPLICIT_ANY.as_str()),
    "must not emit TS7008 when TS7022 applies: {diagnostics:?}"
  );
  // No cascading "object is of type 'unknown'" once circularity resolves to any.
  assert!(
    !diagnostics.iter().any(|d| d.code.as_str() == "TS2571"),
    "unexpected TS2571 after circularity→any: {diagnostics:?}"
  );
}
