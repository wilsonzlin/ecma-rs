//! Private-identifier placement grammar diagnostics:
//! TS18009 / TS18012 / TS18024 / TS18028 / TS18029 / TS18030.

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, name: &str, src: &str) -> Vec<(String, u32, u32, String)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new(name);
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
        d.message.clone(),
      )
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, name: &str, src: &str) -> Vec<String> {
  diags(opts, name, src)
    .into_iter()
    .map(|(c, _, _, _)| c)
    .collect()
}

fn es2015() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  // These tests exercise JS semantic checking (tsc `--checkJs`).
  opts.check_js = Some(true);
  opts
}

fn es5() -> CompilerOptions {
  let mut opts = es2015();
  opts.target = ScriptTarget::Es5;
  opts
}

#[test]
fn private_in_variable_declaration_is_ts18029() {
  // Mirrors conformance `privateNameNotAllowedOutsideClass.ts` /
  // `privateNamesNotAllowedInVariableDeclarations.ts`.
  let src = "const #foo = 3;\n";
  let c = codes(es2015(), "t.ts", src);
  assert_eq!(c, vec!["TS18029".to_string()], "{c:?}");
  let d = diags(es2015(), "t.ts", src);
  let slice = &src[d[0].1 as usize..d[0].2 as usize];
  assert_eq!(slice, "#foo");
}

#[test]
fn private_as_parameter_is_ts18009() {
  // Mirrors conformance `privateNamesNotAllowedAsParameters.ts`.
  let src = "class A {\n    setFoo(#foo: string) {}\n}\n";
  let c = codes(es2015(), "t.ts", src);
  assert_eq!(c.iter().filter(|x| *x == "TS18009").count(), 1, "{c:?}");
  let d = diags(es2015(), "t.ts", src);
  let hit = d.iter().find(|(c, _, _, _)| c == "TS18009").unwrap();
  let slice = &src[hit.1 as usize..hit.2 as usize];
  assert_eq!(slice, "#foo");
}

#[test]
fn private_constructor_name_is_ts18012() {
  // Mirrors conformance `privateNameConstructorReserved.ts`.
  let src = "class A {\n    #constructor() {}\n}\n";
  let c = codes(es2015(), "t.ts", src);
  assert_eq!(c, vec!["TS18012".to_string()], "{c:?}");
  let d = diags(es2015(), "t.ts", src);
  let slice = &src[d[0].1 as usize..d[0].2 as usize];
  assert_eq!(slice, "#constructor");
}

#[test]
fn private_enum_member_is_ts18024() {
  // Mirrors conformance `privateNameEnum.ts`.
  let src = "enum E {\n    #x\n}\n";
  let c = codes(es2015(), "t.ts", src);
  assert_eq!(c, vec!["TS18024".to_string()], "{c:?}");
  let d = diags(es2015(), "t.ts", src);
  let slice = &src[d[0].1 as usize..d[0].2 as usize];
  assert_eq!(slice, "#x");
}

#[test]
fn private_members_under_es5_are_ts18028() {
  // Mirrors conformance `privateNameES5Ban.ts` (subset of member kinds).
  let src = r#"
class A {
    #field = 123;
    #method() {}
    static #sField = "hello";
    static #sMethod() {}
    get #acc() { return ""; }
    set #acc(x: string) {}
    static get #sAcc() { return 0; }
    static set #sAcc(x: number) {}
}
"#;
  let c = codes(es5(), "t.ts", src);
  assert_eq!(c.iter().filter(|x| *x == "TS18028").count(), 8, "{c:?}");
  assert!(c.iter().all(|x| x == "TS18028"), "{c:?}");
}

#[test]
fn optional_chain_private_is_ts18030_not_ts2339() {
  // Mirrors conformance `privateNameUncheckedJsOptionalChain.ts`.
  let src = r#"
class C {
    #bar;
    constructor () {
        this?.#foo;
        this?.#bar;
    }
}
"#;
  let c = codes(es2015(), "t.js", src);
  assert_eq!(c.iter().filter(|x| *x == "TS18030").count(), 2, "{c:?}");
  assert!(
    !c.iter().any(|x| x == "TS2339"),
    "must not fall through to TS2339: {c:?}"
  );
}
