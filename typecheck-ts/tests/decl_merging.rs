use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn interfaces_merge_across_declarations() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("interfaces.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
interface Foo { a: string; }
interface Foo { b: number; }
"#,
    ),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).unwrap();
  let foo_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Foo"))
    .expect("interface Foo present");
  let ty = program.type_of_def(foo_def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("a: string"),
    "merged interface should include property a, got {rendered}"
  );
  assert!(
    rendered.contains("b: number"),
    "merged interface should include property b, got {rendered}"
  );
}

#[test]
fn namespaces_merge_members() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("namespaces.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
export namespace Config { export const a = 1; }
export namespace Config { export const b = 2; }
"#,
    ),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).unwrap();
  let exports = program.exports_of(file_id);
  let config_ty = exports
    .get("Config")
    .and_then(|e| e.type_id)
    .expect("exported Config type");
  let rendered = program.display_type(config_ty).to_string();
  assert!(
    rendered.contains("a: 1"),
    "namespace merge should include first declaration, got {rendered}"
  );
  assert!(
    rendered.contains("b: 2"),
    "namespace merge should include second declaration, got {rendered}"
  );
}

#[test]
fn value_and_namespace_merge_callable_and_members() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("value_namespace.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
export function Lib(x: number): number { return x; }
export namespace Lib { export const version = "1.0.0"; }
export const result = Lib(1);
export const name = Lib.version;
"#,
    ),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).unwrap();
  let exports = program.exports_of(file_id);
  let lib_ty = exports
    .get("Lib")
    .and_then(|e| e.type_id)
    .expect("exported Lib type");
  let rendered = program.display_type(lib_ty).to_string();
  assert!(
    rendered.contains("version"),
    "merged Lib should expose namespace members, got {rendered}"
  );
  assert!(
    rendered.contains("=> number"),
    "merged Lib should remain callable, got {rendered}"
  );

  let result_ty = exports
    .get("result")
    .and_then(|e| e.type_id)
    .expect("result export type");
  assert_eq!(
    program.display_type(result_ty).to_string(),
    "number",
    "call result should be typed"
  );

  let name_ty = exports
    .get("name")
    .and_then(|e| e.type_id)
    .expect("name export type");
  assert!(
    program.display_type(name_ty).to_string().contains("1.0.0")
      || program.display_type(name_ty).to_string().contains("string"),
    "property access through merged namespace should preserve literal type"
  );
}
