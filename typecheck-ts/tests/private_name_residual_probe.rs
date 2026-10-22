//! Residual privateNames burn-down regressions (class-expr init, TS1029,
//! construct-sig merge, contextual field init, getClass self-return).

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn program(src: &str) -> (Program, diagnostics::FileId, String) {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  (program, file_id, src.to_string())
}

fn codes(program: &Program) -> Vec<String> {
  program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect()
}

#[test]
fn class_expr_static_private_call_clean() {
  let (program, _, _) = program(
    r#"
const C = class {
    static #bar() { return 42; }
    static foo() {
        const b = this.#bar();
        return b;
    }
}
"#,
  );
  assert!(codes(&program).is_empty());
}

#[test]
fn async_before_static_ts1029_only() {
  let (program, _, _) = program(
    r#"
const C = class {
    static async #bar() { return 42; }
    static async foo() {
        const b = await this.#bar();
        return b;
    }
    async static *#bazBad() { yield 42; }
}
"#,
  );
  let diags = codes(&program);
  assert!(diags.iter().any(|c| c == "TS1029"), "{diags:?}");
  assert!(
    !diags
      .iter()
      .any(|c| c == "TS2571" || c == "TS18016" || c == "TC2000"),
    "false extras on class-expr private access: {diags:?}"
  );
}

#[test]
fn constructor_signature_new_on_instance() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2022;
  opts.strict_null_checks = true;
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(
    file.clone(),
    r#"
class C { #x = 1; }
interface C { new (): C; }
const y = new C();
const z = new y();
"#,
  );
  let program = Program::new(host, vec![file]);
  assert!(codes(&program).is_empty());
}

#[test]
fn assertion_field_contextual_typing() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2022;
  opts.strict_null_checks = true;
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(
    file.clone(),
    r#"class C { #f: (x: number) => void = x => { x.toFixed(); }; }"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = codes(&program);
  assert!(
    !diags.iter().any(|c| c == "TC3000" || c == "TS7006"),
    "{diags:?}"
  );
}

#[test]
fn new_via_getclass_private_method_clean() {
  let (program, _, _) = program(
    r#"
class AA {
    static #method() { this.x = 10; };
    static #method2(a, ...b) {};
    static x = 1;
    test() {
        new AA.#method();
        const b = new AA.#method2(0, 1, 3);
        const b2 = new (AA.getClass().#method2)(0, 1, 3);
    }
    static getClass() { return AA; }
}
"#,
  );
  let diags = codes(&program);
  assert!(!diags.iter().any(|c| c == "TS2350"), "{diags:?}");
}
