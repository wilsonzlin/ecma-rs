use typecheck_ts::DefId;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn resolves_types_from_namespace_imports_through_reexports() {
  let mut host = MemoryHost::new();
  let m_key = FileKey::new("m.ts");
  host.insert(m_key.clone(), "export interface Foo { x: number; }");

  let re_key = FileKey::new("re.ts");
  host.insert(re_key.clone(), "export * from \"./m\";");

  let a_key = FileKey::new("a.ts");
  let a_src = "import * as NS from \"./re\";\nlet v: NS.Foo;\nconst use = v.x;\n";
  host.insert(a_key.clone(), a_src);

  let program = Program::new(host, vec![a_key.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let m_id = program.file_id(&m_key).unwrap();
  for def in program.definitions_in_file(m_id) {
    let name = program.def_name(def).unwrap_or_default();
    let ty = program
      .display_type(program.type_of_def_interned(def))
      .to_string();
    println!("m def {} ({:?}): {}", name, def, ty);
  }
  println!("all defs:");
  for file in program.files() {
    let key = program.file_key(file).unwrap();
    println!("file {key:?}");
    for def in program.definitions_in_file(file) {
      let name = program.def_name(def).unwrap_or_default();
      println!("  def {:?} {name}", def);
    }
  }
  println!(
    "name for 3652989691: {:?}",
    program.def_name(DefId(3652989691))
  );
  let file_id = program.file_id(&a_key).expect("file id for a.ts");
  let a_defs = program.definitions_in_file(file_id);
  for def in a_defs.iter() {
    let name = program.def_name(*def).unwrap_or_default();
    let ty = program
      .display_type(program.type_of_def_interned(*def))
      .to_string();
    println!("a def {} ({:?}): {}", name, def, ty);
  }
  let re_id = program.file_id(&re_key).unwrap();
  println!("re exports: {:?}", program.exports_of(re_id));
  println!("a exports: {:?}", program.exports_of(file_id));
  let v_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("definition for v");
  let v_ty = program.type_of_def_interned(v_def);
  assert_ne!(
    program.display_type(v_ty).to_string(),
    "unknown",
    "resolved type for v should not be unknown"
  );
  let offset = a_src.find("x;").expect("marker offset") as u32;
  let ty = program.type_at(file_id, offset).expect("type at v.x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn resolves_qualified_types_from_named_imports() {
  let mut host = MemoryHost::new();
  let m_key = FileKey::new("m.ts");
  host.insert(
    m_key,
    "export namespace NS { export interface Foo { x: number; } }\nexport { NS };",
  );

  let a_key = FileKey::new("a.ts");
  let a_src = "import { NS } from \"./m\";\nlet v: NS.Foo;\nconst use = v.x;\n";
  host.insert(a_key.clone(), a_src);

  let program = Program::new(host, vec![a_key.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&a_key).expect("file id for a.ts");
  let v_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("definition for v");
  let v_ty = program.type_of_def_interned(v_def);
  assert_ne!(
    program.display_type(v_ty).to_string(),
    "unknown",
    "resolved type for v should not be unknown"
  );
  let offset = a_src.find("x;").expect("marker offset") as u32;
  let ty = program.type_at(file_id, offset).expect("type at v.x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
