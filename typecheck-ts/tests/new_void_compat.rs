//! `new` on callables whose call signatures return error-recovery types
//! (`unknown`/`any`) is void-compatible, matching tsc's silence under default
//! options — e.g. a private getter returning an unannotated function
//! expression (`privateNameAccessorsCallExpression.ts`).

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
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

#[test]
fn new_on_getter_returning_unannotated_function_is_allowed() {
  // `get #fieldFunc() { return function() { this.x = 10; } }` — the returned
  // function has no return statement (void-compatible). tsc: no error.
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  let src = r#"
class A {
    get #fieldFunc() {  return function() { this.x = 10; } }
    get #fieldFunc2() { return  function(a, ...b) {}; }
    x = 1;
    test() {
        this.#fieldFunc();
        const func = this.#fieldFunc;
        func();
        new this.#fieldFunc();

        const arr = [ 1, 2 ];
        this.#fieldFunc2(0, ...arr, 3);
        const b = new this.#fieldFunc2(0, ...arr, 3);
    }
}
"#;
  assert_eq!(codes(opts, src), Vec::<String>::new());
}

#[test]
fn new_on_non_void_callable_still_reports_ts2350() {
  // A *concrete* non-void return still trips TS2350 (tsc: only void functions
  // can be `new`'d).
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  let src = r#"
declare function f(): number;
new f();
"#;
  assert_eq!(codes(opts, src), vec!["TS2350"]);
}
