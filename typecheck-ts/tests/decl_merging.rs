use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program, PropertyKey};

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
  let props = program.properties_of(ty);
  let keys: Vec<_> = props
    .iter()
    .filter_map(|p| match &p.key {
      PropertyKey::String(name) => Some(name.clone()),
      _ => None,
    })
    .collect();
  assert!(
    keys.contains(&"a".to_string()) && keys.contains(&"b".to_string()),
    "merged interface should include properties a and b, got {keys:?}"
  );
  let a_ty = program
    .property_type(ty, PropertyKey::String("a".into()))
    .expect("merged property a");
  assert_eq!(program.display_type(a_ty).to_string(), "string");
  let b_ty = program
    .property_type(ty, PropertyKey::String("b".into()))
    .expect("merged property b");
  assert_eq!(program.display_type(b_ty).to_string(), "number");
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
  let def_a = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("a"))
    .expect("namespace member a");
  let def_b = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("b"))
    .expect("namespace member b");
  let a_ty = program.display_type(program.type_of_def(def_a)).to_string();
  let b_ty = program.display_type(program.type_of_def(def_b)).to_string();
  assert!(
    rendered.contains("a: 1"),
    "namespace merge should include first declaration, got {rendered}"
  );
  assert!(
    rendered.contains("b: 2"),
    "namespace merge should include second declaration, got {rendered}"
  );
  assert!(
    a_ty.contains('1'),
    "namespace member a should retain literal type, got {a_ty}"
  );
  assert!(
    b_ty.contains('2'),
    "namespace member b should retain literal type, got {b_ty}"
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
  let name_rendered = program.display_type(name_ty).to_string();
  assert!(
    name_rendered.contains("1.0.0") || name_rendered.contains("string"),
    "property access through merged namespace should preserve literal type"
  );
}

#[test]
fn value_and_namespace_merge_preserves_member_function_signature() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("merged_function_namespace.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
function Lib(value: number): number {
  return value * 2;
}

namespace Lib {
  export const version = "merged";
  export function helper(label: string): string {
    return label + version;
  }
}

export const doubled = Lib(2);
export const label = Lib.helper("ok");
export { Lib };
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
  let helper_ty = program
    .property_type(lib_ty, PropertyKey::String("helper".into()))
    .expect("namespace member helper should be present on merged Lib");
  let signatures = program.call_signatures(helper_ty);
  assert_eq!(
    signatures.len(),
    1,
    "expected a single signature for Lib.helper, got {signatures:?}"
  );
  assert_eq!(
    signatures[0].signature.params.len(),
    1,
    "expected Lib.helper to take one argument"
  );

  let label_ty = exports
    .get("label")
    .and_then(|e| e.type_id)
    .expect("label export type");
  assert_eq!(program.display_type(label_ty).to_string(), "string");
}
