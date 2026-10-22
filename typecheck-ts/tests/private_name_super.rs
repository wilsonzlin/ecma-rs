//! TS2376 / TS17009 — `this` before `super()` with private identifiers.

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, u32, u32)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| {
      (
        d.code.as_str().to_string(),
        d.primary.range.start,
        d.primary.range.end,
      )
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  diags(opts, src).into_iter().map(|(c, _, _)| c).collect()
}

fn es2015() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts.use_define_for_class_fields = true;
  opts
}

fn esnext_native_fields() -> CompilerOptions {
  let mut opts = es2015();
  opts.target = ScriptTarget::EsNext;
  opts.use_define_for_class_fields = true;
  opts
}

#[test]
fn this_before_super_with_private_is_ts2376_and_ts17009() {
  // Mirrors conformance `privateNameBadSuper.ts` (ES2015).
  let src = r#"
class B {}
class A extends B {
  #x;
  constructor() {
    this;
    super();
  }
}
"#;
  let d = diags(es2015(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _)| c.clone()).collect();
  assert_eq!(
    c.iter().filter(|x| *x == "TS2376").count(),
    1,
    "expected TS2376: {c:?}"
  );
  assert_eq!(
    c.iter().filter(|x| *x == "TS17009").count(),
    1,
    "expected TS17009: {c:?}"
  );
  let ts2376 = d.iter().find(|(c, _, _)| c == "TS2376").unwrap();
  assert_eq!(&src[ts2376.1 as usize..ts2376.2 as usize], "constructor");
  let ts17009 = d.iter().find(|(c, _, _)| c == "TS17009").unwrap();
  assert_eq!(&src[ts17009.1 as usize..ts17009.2 as usize], "this");
}

#[test]
fn void_before_super_with_private_is_ok() {
  // Mirrors conformance `privateNameLateSuper.ts` — statements before `super`
  // are fine when they do not touch `this` / `super`.
  let src = r#"
class B {}
class A extends B {
  #x;
  constructor() {
    void 0;
    super();
  }
}
"#;
  let c = codes(es2015(), src);
  assert!(
    !c.iter().any(|x| x == "TS2376" || x == "TS17009"),
    "late super without this access must be quiet: {c:?}"
  );
}

#[test]
fn native_define_fields_suppresses_ts2376_keeps_ts17009() {
  // Under ESNext + useDefineForClassFields, tsc drops TS2376 but keeps TS17009.
  let src = r#"
class B {}
class A extends B {
  #x;
  constructor() {
    this;
    super();
  }
}
"#;
  let c = codes(esnext_native_fields(), src);
  assert!(
    !c.iter().any(|x| x == "TS2376"),
    "native class fields suppress TS2376: {c:?}"
  );
  assert_eq!(
    c.iter().filter(|x| *x == "TS17009").count(),
    1,
    "expected TS17009 under native fields: {c:?}"
  );
}
