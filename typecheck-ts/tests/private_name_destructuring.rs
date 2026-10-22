//! Destructuring-assignment typing (tsc
//! `privateNameStaticFieldDestructuredBinding.ts`):
//!
//! - Defaults replace a missing/`undefined` slot with the default's type
//!   (`union(unknown, T)` must never absorb to `unknown`).
//! - Array literals in destructuring positions infer *tuples*, so
//!   `[x, [y]] = [1, [2]]` destructures positionally.
//! - A `this.<unannotated field>` receiver for a private-identifier access
//!   recovers from its initializer (`otherClass = A` → `typeof A`).

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

#[test]
fn destructuring_default_replaces_missing_slot() {
  let src = r#"
class A {
    static #field = 1;
    constructor() {
        ({ a: A.#field = 1, b: [A.#field = 1] } = { b: [] });
        [A.#field = 2] = [];
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn array_literal_in_destructuring_infers_tuple() {
  let src = r#"
class A {
    static #field = 1;
    constructor() {
        [A.#field, [A.#field]] = [1, [2]];
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn self_referential_field_recovers_for_private_access() {
  let src = r#"
class A {
    static #field = 1;
    otherClass = A;
    constructor() {
        [this.otherClass.#field = 2] = [];
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn full_conformance_shape() {
  let src = r#"
class A {
    static #field = 1;
    otherClass = A;
    testObject() {
        return { x: 10, y: 6 };
    }
    testArray() {
        return [10, 11];
    }
    constructor() {
        let y: number;
        ({ x: A.#field, y } = this.testObject());
        ([A.#field, y] = this.testArray());
        ({ a: A.#field, b: [A.#field] } = { a: 1, b: [2] });
        [A.#field, [A.#field]] = [1, [2]];
        ({ a: A.#field = 1, b: [A.#field = 1] } = { b: [] });
        [A.#field = 2] = [];
        [this.otherClass.#field = 2] = [];
    }
    static test(_a: typeof A) {
        [_a.#field] = [2];
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}
