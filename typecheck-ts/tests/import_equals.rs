use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn import_equals_entity_name_aliases_value() {
  let mut host = MemoryHost::new();
  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
namespace Bar { export const Baz = 1 as const; }
import Foo = Bar.Baz;
export const x = Foo;
"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

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
fn import_equals_require_aliases_module_namespace() {
  let mut host = MemoryHost::new();
  let dep = FileKey::new("dep.ts");
  host.insert(dep, "export const value: number = 1;");

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"import Foo = require("./dep"); export const x = Foo.value;"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
