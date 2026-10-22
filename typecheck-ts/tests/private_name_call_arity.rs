//! TS2554 / TS2345 on private method calls; TS2322 on private field assigns;
//! private static fields ignored in unmatched-property assignability (TS2739).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
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

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, u32, u32, String)> {
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
        src[d.primary.range.start as usize..d.primary.range.end as usize].to_string(),
      )
    })
    .collect();
  out.sort_by(|a, b| (a.0.as_str(), a.1, a.2).cmp(&(b.0.as_str(), b.1, b.2)));
  out
}

fn strict() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn private_method_wrong_arg_and_arity() {
  // Mirrors conformance `privateNameMethod.ts`.
  let src = r#"
class A1 {
    #method(param: string): string {
        return "";
    }
    constructor(name: string) {
        this.#method("")
        this.#method(1) // Error
        this.#method()  // Error
    }
}
"#;
  let d = diags(strict(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _, _)| c.clone()).collect();
  assert!(c.iter().any(|x| x == "TS2345"), "expected TS2345: {d:?}");
  assert!(c.iter().any(|x| x == "TS2554"), "expected TS2554: {d:?}");
  assert!(
    !c.iter().any(|x| x == "TC2000"),
    "arity must not stay TC2000: {d:?}"
  );
  let arity: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS2554").collect();
  assert_eq!(arity.len(), 1, "{d:?}");
  assert_eq!(arity[0].3, "#method", "TS2554 spans private name: {d:?}");
}

#[test]
fn private_static_method_wrong_arg_and_arity() {
  // Mirrors conformance `privateNameStaticMethod.ts`.
  let src = r#"
class A1 {
    static #method(param: string): string {
        return "";
    }
    constructor() {
        A1.#method("")
        A1.#method(1) // Error
        A1.#method()  // Error
    }
}
"#;
  let d = diags(strict(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _, _)| c.clone()).collect();
  assert!(c.iter().any(|x| x == "TS2345"), "{d:?}");
  assert!(c.iter().any(|x| x == "TS2554"), "{d:?}");
  assert!(!c.iter().any(|x| x == "TC2000"), "{d:?}");
  let arity: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS2554").collect();
  assert_eq!(arity[0].3, "#method", "{d:?}");
}

#[test]
fn private_field_string_to_number_is_ts2322() {
  // Mirrors conformance `privateNameFieldsESNext.ts` (`this.#a = "hello"`).
  let mut opts = strict();
  opts.use_define_for_class_fields = false;
  let src = r#"
class C {
    #a = 10;
    method() {
        this.#a = "hello";
    }
}
"#;
  let c = codes(opts, src);
  assert!(c.iter().any(|x| x == "TS2322"), "expected TS2322: {c:?}");
}

#[test]
fn typeof_class_empty_class_ignores_private_statics() {
  // Mirrors conformance `privateNamesAndStaticFields.ts` OK-for-now assign.
  let src = r#"
class A {
    static #foo: number;
    static #bar: number;
}
const willErrorSomeDay: typeof A = class {};
"#;
  let c = codes(strict(), src);
  assert!(
    !c.iter()
      .any(|x| x == "TS2739" || x == "TS2741" || x == "TS2322"),
    "private statics must not count as unmatched: {c:?}"
  );
}
