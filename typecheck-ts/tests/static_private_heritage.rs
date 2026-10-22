//! Static private names do not participate in heritage: `B.#foo` targets
//! B's *own* private (TS18013 from a foreign class), and inherited static
//! privates don't exist on `typeof B` (TS2339) — tsc
//! `checkPrivateIdentifierPropertyAccess` / `privateNamesAndStaticFields.ts`.
//! Instance privates still follow the heritage rule (`b.#foo` inside the base
//! is allowed when the receiver derives from the lexical declarer).

use typecheck_ts::{FileKey, MemoryHost, Program};

fn check(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
  let file = FileKey::new("a.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| format!("{}@{}", d.code.as_str(), d.primary.range.start))
    .collect();
  out.sort();
  out
}

#[test]
fn probe_static_private() {
  // Exact conformance shape (tsc: TS18013 on B.#foo, TS2339 on B.#bar).
  let src = r#"class A {
    static #foo: number;
    static #bar: number;
    constructor () {
        A.#foo = 3;
        B.#foo; // Error
        B.#bar; // Error
    }
}

class B extends A {
    static #foo: string;
    constructor () {
        super();
        B.#foo = "some string";
    }
}
"#;
  let d = check(src);
  eprintln!("static_private_case: {:?}", d);
  assert_eq!(
    d,
    ["TS18013@111", "TS2339@136"],
    "expected TS18013 + TS2339, got {d:?}"
  );

  // Instance heritage still allowed (regression guard for private_name_heritage).
  let d2 = check(
    r#"class A {
    #foo(a: number) {}
    m(b: B) { b.#foo(30); }
}
class B extends A {
    #foo(a: string) {}
}
"#,
  );
  eprintln!("instance_heritage: {:?}", d2);
  assert!(
    d2.is_empty(),
    "instance heritage access must stay allowed, got {d2:?}"
  );

  // Own-class static access unaffected.
  let d3 = check(
    r#"class A {
    static #foo: number = 1;
    static m() { return A.#foo; }
}
"#,
  );
  eprintln!("own_static: {:?}", d3);
  assert!(
    d3.is_empty(),
    "own-class static access must be clean, got {d3:?}"
  );
}
