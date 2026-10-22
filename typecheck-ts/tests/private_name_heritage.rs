//! Private-identifier visibility across a class hierarchy (tsc
//! `checkPrivateIdentifierPropertyAccess`):
//!
//! - `this.#foo` inside a derived class resolves to the derived class's own
//!   declaration, even when the base declares the same spelling
//!   (`privateNamesAndMethods.ts`).
//! - `b.#foo` inside the base class is allowed when the receiver derives
//!   from the lexical declarer (the lexical private is in its heritage).
//! - Access from outside any class is TS18013.
//! - Async generators require the global `AsyncIterableIterator` (a lib
//!   availability check, not a target check: `--target es2015 --lib esnext`
//!   accepts them; tsc).

use typecheck_ts::lib_support::{CompilerOptions, LibName, ScriptTarget};
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
fn derived_class_shadowed_private_resolves_lexically() {
  let src = r#"
class A {
    #foo(a: number) {}
    async #bar(a: number) {}
    async *#baz(a: number) {
        return 3;
    }
    #_quux: number;
    get #quux (): number {
        return this.#_quux;
    }
    set #quux (val: number) {
        this.#_quux = val;
    }
    constructor () {
        this.#foo(30);
        this.#bar(30);
        this.#baz(30);
        this.#quux = this.#quux + 1;
        this.#quux++;
 }
}

class B extends A {
    #foo(a: string) {}
    constructor () {
        super();
        this.#foo("str");
    }
}
"#;
  let mut opts = CompilerOptions::default();
  opts.libs = vec![LibName::parse("esnext").unwrap()];
  assert_eq!(codes(opts, src), Vec::<String>::new());
}

#[test]
fn base_method_may_access_shadowed_private_on_derived_receiver() {
  // tsc: the lexical private (A.#foo) is in B's heritage, so `b.#foo` is fine.
  let src = "class A { #foo(a: number) {} m(b: B) { b.#foo(1); } }\nclass B extends A { #foo(a: string) {} }\n";
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn outside_private_access_is_ts18013() {
  let src = "class A { #foo(a: number) {} }\ndeclare const a: A;\na.#foo(1);\n";
  assert!(
    codes(CompilerOptions::default(), src)
      .iter()
      .any(|x| x == "TS18013"),
    "outside private access must be TS18013"
  );
}

#[test]
fn async_generator_requires_async_iterable_iterator_lib() {
  let src = "class A {\n  async *#baz(a: number) { return 3; }\n}\n";

  // Default (es2015) libs lack AsyncIterableIterator → TS2318 (tsc).
  let mut default_opts = CompilerOptions::default();
  default_opts.target = ScriptTarget::Es2015;
  assert!(
    codes(default_opts, src).iter().any(|x| x == "TS2318"),
    "missing lib global must be TS2318"
  );

  // `--target es2015 --lib esnext`: the global exists → no TS2318 (tsc).
  let mut esnext_opts = CompilerOptions::default();
  esnext_opts.target = ScriptTarget::Es2015;
  esnext_opts.libs = vec![LibName::parse("esnext").unwrap()];
  assert_eq!(codes(esnext_opts, src), Vec::<String>::new());
}
