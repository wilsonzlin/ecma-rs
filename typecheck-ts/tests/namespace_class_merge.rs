//! Merged ambient namespace+class resolution (conformance
//! `internalModules/DeclarationMerging/AmbientModuleAndAmbientWithSameNameAndCommonRoot.ts`):
//!
//! - Class/enum members of a namespace contribute their *value* side
//!   (constructor + statics from the synthetic value def), not the instance
//!   type stored under the class def (`new N.C(0)` is constructable).
//! - Cross-file declarations of the same namespace combine into one member
//!   view for *every* participating decl, so whichever decl a body seeds
//!   from, `A.Point.Origin` and `new A.Point(...)` resolve.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(files: &[(&str, &str)]) -> Vec<String> {
  let mut host = MemoryHost::new();
  let mut keys = Vec::new();
  for (name, src) in files {
    let k = FileKey::new(*name);
    host.insert(k.clone(), *src);
    keys.push(k);
  }
  let program = Program::new(host, keys);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

const MODULE_DTS: &str = "declare namespace A {\n    export namespace Point {\n        export var Origin: {\n            x: number;\n            y: number;\n        }\n    }\n}\n";
const CLASS_DTS: &str = "declare namespace A {\n    export class Point {\n        constructor(x: number, y: number);\n        x: number;\n        y: number;\n    }\n}\n";
const TEST_TS: &str =
  "var p: { x: number; y: number; }\nvar p = A.Point.Origin;\nvar p = new A.Point(0, 0);\n";

#[test]
fn ambient_namespace_and_class_merge_cross_file() {
  assert_eq!(
    codes(&[
      ("module.d.ts", MODULE_DTS),
      ("class.d.ts", CLASS_DTS),
      ("test.ts", TEST_TS)
    ]),
    Vec::<String>::new()
  );
}

#[test]
fn ambient_namespace_and_class_merge_single_file() {
  let single = "declare namespace A {\n    export namespace Point {\n        export var Origin: {\n            x: number;\n            y: number;\n        }\n    }\n    export class Point {\n        constructor(x: number, y: number);\n        x: number;\n        y: number;\n    }\n}\n";
  assert_eq!(
    codes(&[("single.d.ts", single), ("test.ts", TEST_TS)]),
    Vec::<String>::new()
  );
}

#[test]
fn nested_namespace_class_is_constructable() {
  let src = "declare namespace N {\n  export class C {\n    constructor(x: number);\n    x: number;\n  }\n}\nvar c = new N.C(1);\n";
  assert_eq!(codes(&[("t.ts", src)]), Vec::<String>::new());
}

#[test]
fn cross_file_namespace_members_combine() {
  // Both decls must see the combined member list regardless of which one a
  // body seeds from (previously one side built an empty object).
  let f1 = "declare namespace M {\n  export var a: number;\n}\n";
  let f2 = "declare namespace M {\n  export var b: string;\n}\n";
  let t = "var na: number = M.a;\nvar nb: string = M.b;\n";
  assert_eq!(
    codes(&[("f1.d.ts", f1), ("f2.d.ts", f2), ("t.ts", t)]),
    Vec::<String>::new()
  );
}

#[test]
fn cross_file_namespace_wrong_member_type_still_errors() {
  let f1 = "declare namespace M {\n  export var a: number;\n}\n";
  let f2 = "declare namespace M {\n  export var b: string;\n}\n";
  let t = "var na: string = M.a;\n";
  let c = codes(&[("f1.d.ts", f1), ("f2.d.ts", f2), ("t.ts", t)]);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "combined members keep their declared types: {c:?}"
  );
}

#[test]
fn cross_file_ambient_class_is_constructable() {
  // Global value bindings for a class in another file must map to the
  // synthetic value def (constructor + statics), not the instance type.
  let a =
    "declare class Point {\n  constructor(x: number, y: number);\n  x: number;\n  y: number;\n}\n";
  let t = "var p = new Point(0, 0);\nvar q: { x: number; y: number } = p;\n";
  assert_eq!(codes(&[("a.d.ts", a), ("t.ts", t)]), Vec::<String>::new());
}

#[test]
fn cross_file_ambient_class_wrong_args_still_error() {
  let a =
    "declare class Point {\n  constructor(x: number, y: number);\n  x: number;\n  y: number;\n}\n";
  let t = "var p = new Point(0);\n";
  let c = codes(&[("a.d.ts", a), ("t.ts", t)]);
  assert!(
    c.iter()
      .any(|x| x == "TS2554" || x == "TS2345" || x == "TC2000"),
    "constructor arity must still be checked: {c:?}"
  );
}
