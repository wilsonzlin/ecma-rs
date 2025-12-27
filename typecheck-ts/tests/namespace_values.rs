use typecheck_ts::{FileKey, MemoryHost, Program, PropertyKey};

#[test]
fn namespace_value_members_use_declared_types() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("a.ts");
  let src = r#"namespace N { export const x: string = "hi"; }
const y = N.x;
"#;
  host.insert(file.clone(), src);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id for a.ts");
  let offset = src.find("N.x").expect("offset for N.x") as u32 + 2;
  let ty = program.type_at(file_id, offset).expect("type at N.x");
  assert_eq!(program.display_type(ty).to_string(), "string");
}

#[test]
fn namespace_excludes_type_only_members_from_values() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("a.ts");
  let src = r#"namespace N { export interface I {} }
const value = N.I;
"#;
  host.insert(file.clone(), src);

  let program = Program::new(host, vec![file.clone()]);
  let _diagnostics = program.check();

  let file_id = program.file_id(&file).expect("file id for a.ts");
  let ns_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("N"))
    .expect("namespace definition");
  let ns_ty = program.type_of_def_interned(ns_def);
  let props = program.properties_of(ns_ty);
  assert!(
    props
      .iter()
      .all(|prop| { !matches!(&prop.key, PropertyKey::String(name) if name == "I") }),
    "namespace should not expose interface members as values"
  );

  let offset = src.find("N.I").expect("offset for N.I") as u32 + 2;
  let ty = program.type_at(file_id, offset).expect("type at N.I");
  assert_eq!(program.display_type(ty).to_string(), "unknown");
}
