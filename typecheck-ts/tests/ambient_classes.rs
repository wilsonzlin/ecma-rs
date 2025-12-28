use std::sync::Arc;

use typecheck_ts::lib_support::{FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn ambient_class_members_from_libs() {
  let parsed = parse_js::parse("declare class Box<T> { value: T }").unwrap();
  if let Some(stmt) = parsed.stx.body.first() {
    match stmt.stx.as_ref() {
      parse_js::ast::stmt::Stmt::AmbientClassDecl(class) => {
        println!(
          "parsed ambient class type params present: {} members {}",
          class
            .stx
            .type_parameters
            .as_ref()
            .map(|p| p.len())
            .unwrap_or(0),
          class.stx.members.len()
        );
      }
      parse_js::ast::stmt::Stmt::ClassDecl(class) => {
        println!(
          "parsed runtime class with type params {} members {}",
          class
            .stx
            .type_parameters
            .as_ref()
            .map(|p| p.len())
            .unwrap_or(0),
          class.stx.members.len()
        );
      }
      other => {
        println!("parsed other stmt: {:?}", other);
      }
    }
  }

  let mut host = MemoryHost::new();
  let lib_key = FileKey::new("box.d.ts");
  host.add_lib(LibFile {
    key: lib_key.clone(),
    name: Arc::from("box.d.ts".to_string()),
    kind: FileKind::Dts,
    text: Arc::from("declare class Box<T> { value: T }".to_string()),
  });

  let file = FileKey::new("index.ts");
  host.insert(
    file.clone(),
    Arc::from("let b: Box<string>;\nconst v = b.value;".to_string()),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  println!("diagnostics: {:?}", diagnostics);
  let lib_ids = program.file_ids_for_key(&lib_key);
  for lib_id in lib_ids.iter().copied() {
    println!("lib file {lib_id:?} defs:");
    for def in program.definitions_in_file(lib_id) {
      let name = program.def_name(def).unwrap_or_default();
      let ty = program.display_type(program.type_of_def(def)).to_string();
      let interned = program.display_type(program.type_of_def_interned(def)).to_string();
      let kind = program.interned_type_kind(program.type_of_def_interned(def));
      let prop_ty_kind = program
        .property_type(program.type_of_def_interned(def), typecheck_ts::PropertyKey::String("value".into()))
        .map(|t| program.interned_type_kind(t));
      let props: Vec<_> = program
        .properties_of(program.type_of_def_interned(def))
        .into_iter()
        .map(|p| (p.key, program.display_type(p.ty).to_string()))
        .collect();
      println!(
        "  def {:?} name {} type {} interned {} kind {:?} prop_ty {:?} props {:?}",
        def, name, ty, interned, kind, prop_ty_kind, props
      );
    }
  }
  if let Some(box_def) = lib_ids
    .iter()
    .flat_map(|id| program.definitions_in_file(*id))
    .find(|d| program.def_name(*d) == Some("Box".into()))
  {
    let box_ty = program.type_of_def_interned(box_def);
    let props: Vec<_> = program
      .properties_of(box_ty)
      .into_iter()
      .map(|p| (p.key, program.interned_type_kind(p.ty)))
      .collect();
    println!("Box properties {:?}", props);
    println!(
      "Box.value kind {:?}",
      program.property_type(box_ty, typecheck_ts::PropertyKey::String("value".into())).map(|t| program.interned_type_kind(t))
    );
  }
  let source_id = program.file_id(&file).unwrap();
  println!("source defs:");
  for def in program.definitions_in_file(source_id) {
    let name = program.def_name(def).unwrap_or_default();
    let ty = program.display_type(program.type_of_def(def)).to_string();
    let interned = program.display_type(program.type_of_def_interned(def)).to_string();
    let kind = program.interned_type_kind(program.type_of_def_interned(def));
    let prop_ty_kind = program
      .property_type(program.type_of_def_interned(def), typecheck_ts::PropertyKey::String("value".into()))
      .map(|t| program.interned_type_kind(t));
    let props: Vec<_> = program
      .properties_of(program.type_of_def_interned(def))
      .into_iter()
      .map(|p| (p.key, program.display_type(p.ty).to_string()))
      .collect();
    println!(
      "  def {:?} name {} type {} interned {} kind {:?} prop_ty {:?} props {:?}",
      def, name, ty, interned, kind, prop_ty_kind, props
    );
  }
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).unwrap();
  let source = program.file_text(file_id).unwrap();
  let offset = source.find("value").expect("value offset") as u32;
  let ty = program.type_at(file_id, offset).expect("type at value");
  assert_eq!(program.display_type(ty).to_string(), "string");
}
