//! `super` in member position resolves to the base class constructor (static
//! context) or the base instance (instance context), so `super.func()` gets
//! the base method's real return type (`superPropertyAccessNoError.ts`).
//! `super()` calls are still typed `void` by the call path.

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
fn super_instance_method_call_return() {
  let src = "class B {\n    func() {\n        return '';\n    }\n}\nclass D extends B {\n    m() {\n        var x = super.func();\n        var x: string;\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn super_static_method_call_return() {
  let src = "class B {\n    static func() {\n        return 3;\n    }\n}\nclass D extends B {\n    static m() {\n        var x = super.func();\n        var x: number;\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn super_in_instance_accessor() {
  let src = "class B {\n    func() {\n        return '';\n    }\n}\nclass D extends B {\n    get a() {\n        var x = super.func();\n        var x: string;\n        return null;\n    }\n    set a(n) {\n        var x = super.func();\n        var x: string;\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn super_in_static_accessor() {
  let src = "class B {\n    static func() {\n        return 3;\n    }\n}\nclass D extends B {\n    static get a() {\n        var x = super.func();\n        var x: number;\n        return null;\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn super_wrong_return_still_errors() {
  // Base returns string; assigning to number must still error.
  let src = "class B {\n    func() {\n        return '';\n    }\n}\nclass D extends B {\n    m() {\n        var x = super.func();\n        var x: number;\n    }\n}\n";
  assert_eq!(codes(src), ["TS2403"]);
}

#[test]
fn super_in_static_field_initializers() {
  // Static field inits: super is the base constructor — static `a: any` is
  // readable, writable, and callable as a template tag
  // (`thisAndSuperInStaticMembers2.ts`).
  let src = "declare class B {\n    static a: any;\n    static f(): number;\n    a: number;\n    f(): number;\n}\nclass C extends B {\n    static z1 = super.a;\n    static z3 = super.f();\n    static z5 = super.a = 0;\n    static z6 = super.a += 1;\n    static z7 = (() => { super.a = 0; })();\n    static z14 = ++super.a;\n    static z18 = super.a``;\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn super_in_static_block() {
  let src = "declare class B {\n    static a: any;\n}\nclass C extends B {\n    static {\n        super.a = 1;\n    }\n}\n";
  assert!(codes(src).is_empty());
}
