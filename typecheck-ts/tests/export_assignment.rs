use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn export_assignment_interops_with_import_equals_require() {
  let mut host = MemoryHost::new();
  let dep = FileKey::new("dep.ts");
  host.insert(
    dep.clone(),
    r#"
declare function Foo(): 1;
declare namespace Foo {
  export interface Bar {
    x: number;
  }
}
export = Foo;
"#,
  );

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
import Foo = require("./dep");

export const x = Foo();

const y: Foo.Bar = { x: 123 };
y.x satisfies number;
"#,
  );
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn export_assignment_accepts_qualified_name_rhs() {
  let mut host = MemoryHost::new();
  let dep = FileKey::new("dep.ts");
  host.insert(
    dep.clone(),
    r#"
declare namespace Outer {
  export const inner: 1;
}
export = Outer.inner;
"#,
  );

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
import v = require("./dep");
export const x = v;
x satisfies 1;
"#,
  );
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn export_assignment_errors_when_mixed_with_other_exports() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  host.insert(
    file.clone(),
    r#"
const Foo = 1;
export = Foo;
export const x = 2;
"#,
  );

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics.iter().any(|d| d.code.as_str() == "TS2309"),
    "expected TS2309 for mixed export assignment, got {diagnostics:?}"
  );
}
