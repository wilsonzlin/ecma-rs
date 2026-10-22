//! Lexical resolution of private-identifier *fields* when a derived class
//! redeclares the base's private name with a different type
//! (`privateNamesAndFields.ts`):
//!
//! - tsc keys private names by their declaring class: `class B extends A`
//!   redeclaring `#foo` has *two* slots (A's and B's); accesses in B's scope
//!   resolve to B's declaration, accesses in A's scope to A's.
//! - The instance-type intersection `B & A` is inhabited — the two same-spelled
//!   private slots are distinct, so the intersection must not collapse to
//!   `never` (tsc `getIntersectionType` never reduces on private identifiers).
//! - Arrow concise bodies are AssignmentExpressions: `(getX = a => a.#x, "_")`
//!   parses the comma at the enclosing sequence, not inside the arrow body
//!   (ECMA-262 §14.2 ConciseBody; `privateNameComputedPropertyName2.ts`).

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
fn derived_private_field_shadows_base_slot() {
  // Exact conformance shape (`privateNamesAndFields.ts`, @strict @target es6):
  // each class's accesses resolve to its own `#foo` — no diagnostics.
  let src = r#"
class A {
    #foo: number;
    constructor () {
        this.#foo = 3;
    }
}

class B extends A {
    #foo: string;
    constructor () {
        super();
        this.#foo = "some string";
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn shadowed_private_field_read_uses_derived_declaration_type() {
  // Inside B, `this.#foo` is B's slot (string), not the intersection
  // `string & number` (never): assigning to `number` is TS2322, and the
  // receiver is not collapsed to `never` (no bogus TS2339).
  let src = r#"
class A {
    #foo: number = 0;
}
class B extends A {
    #foo: string = "";
    m() {
        const n: number = this.#foo;
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), vec!["TS2322"]);
}

#[test]
fn shadowed_private_field_write_checks_derived_declaration_type() {
  // Writes target B's slot: `42` is not assignable to `string` (TS2322).
  let src = r#"
class A {
    #foo: number = 0;
}
class B extends A {
    #foo: string = "";
    m() {
        this.#foo = 42;
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), vec!["TS2322"]);
}

#[test]
fn derived_instance_stays_assignable_to_base() {
  // B's instance intersection must not collapse to `never`: `new B()` is still
  // assignable to `A` (B carries A's private slot through heritage).
  let src = r#"
class A {
    #foo: number = 0;
}
class B extends A {
    #foo: string = "";
}
const a: A = new B();
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn arrow_concise_body_excludes_enclosing_comma() {
  // `privateNameComputedPropertyName2.ts`: the comma in the computed key is the
  // enclosing sequence, not the arrow body — `getX` is the arrow, so its only
  // diagnostic is TS2454 (used before assigned), no false TS2322.
  let src = r#"
let getX: (a: A) => number;

class A {
    #x = 100;
    [(getX = (a: A) => a.#x, "_")]() {}
}

console.log(getX(new A));
"#;
  assert_eq!(codes(CompilerOptions::default(), src), vec!["TS2454"]);
}
