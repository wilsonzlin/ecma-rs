//! `this` inside static members resolves to the class constructor value type
//! (including construct signatures and statics), so `var t = this; new t(…)`
//! is constructable (`typeOfThisInStaticMembers.ts`). Class *declarations*
//! resolve through the same span-keyed map as class expressions — the body's
//! scope chain does not always carry the file-level class binding (e.g. when
//! checking a method body via `type_of_def`).

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
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
fn new_on_static_this_alias_is_constructable() {
  let src = "class C {\n    constructor(x: number) { }\n    static foo: number;\n    static bar() {\n        var t = this;\n        return this;\n    }\n}\nvar t = C.bar();\nvar r2 = t.foo + 1;\nvar r3 = t.bar();\nvar r4 = new t(1);\n";
  assert!(codes(src).is_empty());
}

#[test]
fn generic_class_static_this_alias() {
  let src = "class C2<T> {\n    static test: number;\n    constructor(x: string) { }\n    static foo: string;\n    static bar() {\n        var t = this;\n        return this;\n    }\n}\nvar t2 = C2.bar();\nvar r5 = t2.foo;\nvar r6 = t2.bar();\nvar r7 = new t2('');\n";
  assert!(codes(src).is_empty());
}
