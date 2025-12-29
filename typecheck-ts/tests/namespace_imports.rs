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
  println!("diagnostics: {diagnostics:?}");
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let m_id = program
    .file_id(&FileKey::new("m.ts"))
    .expect("file id for m.ts");
  let exports = program.exports_of(m_id);
  if let Some(entry) = exports.get("NS") {
    println!(
      "export NS def {:?} type {:?}",
      entry.def,
      entry.type_id.map(|t| program.display_type(t).to_string())
    );
    if let Some(def) = entry.def {
      println!(
        "export NS type kind {:?}",
        program.interned_type_kind(program.type_of_def_interned(def))
      );
    }
  }
  for def in program.definitions_in_file(m_id) {
    println!(
      "m.ts def {:?} name {:?} kind {:?}",
      def,
      program.def_name(def),
      program.interned_type_kind(program.type_of_def_interned(def))
    );
    if program.def_name(def).as_deref() == Some("Foo") {
      let ty = program.type_of_def_interned(def);
      println!(
        "Foo props {:?}",
        program
          .properties_of(ty)
          .iter()
          .map(|p| (p.key.clone(), program.display_type(p.ty).to_string()))
          .collect::<Vec<_>>()
      );
    }
  }

  let file_id = program.file_id(&a_key).expect("file id for a.ts");
  let v_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("definition for v");
  let v_ty = program.type_of_def_interned(v_def);
  println!("v type {}", program.display_type(v_ty));
  println!("v kind {:?}", program.interned_type_kind(v_ty));
  assert_ne!(
    program.display_type(v_ty).to_string(),
    "unknown",
    "resolved type for v should not be unknown"
  );
  let offset = a_src.find("x;").expect("marker offset") as u32;
  let expr_at = program.expr_at(file_id, offset);
  println!("expr_at {expr_at:?}");
  let ty = program.type_at(file_id, offset).expect("type at v.x");
  println!("type at v.x {}", program.display_type(ty));
  let body = program.file_body(file_id);
  println!("file body: {body:?}");
  if let Some(body_id) = body.or(expr_at.map(|(b, _)| b)) {
    let res = program.check_body(body_id);
    if let Some(obj_ty) = res.expr_type(typecheck_ts::ExprId(0)) {
      println!("expr0 kind {:?}", program.interned_type_kind(obj_ty));
    }
    for (idx, span) in res.expr_spans().iter().enumerate() {
      if let Some(ty) = res.expr_type(typecheck_ts::ExprId(idx as u32)) {
        println!("{idx}: {span:?} -> {}", program.display_type(ty));
      }
    }
  }
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
  println!("diagnostics: {diagnostics:?}");
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let m_id = program.file_id(&FileKey::new("m.ts")).expect("m file id");
  let exports = program.exports_of(m_id);
  println!("exports keys {:?}", exports.keys().collect::<Vec<_>>());
  if let Some(entry) = exports.get("NS") {
    println!(
      "export NS def {:?} type {:?}",
      entry.def,
      entry.type_id.map(|t| program.display_type(t).to_string())
    );
  }
  for def in program.definitions_in_file(m_id) {
    println!(
      "m.ts def {:?} name {:?} kind {:?}",
      def,
      program.def_name(def),
      program.interned_type_kind(program.type_of_def_interned(def))
    );
    if program.def_name(def).as_deref() == Some("Foo") {
      let ty = program.type_of_def_interned(def);
      println!(
        "Foo props {:?}",
        program
          .properties_of(ty)
          .iter()
          .map(|p| (p.key.clone(), program.display_type(p.ty).to_string()))
          .collect::<Vec<_>>()
      );
    }
  }

  let file_id = program.file_id(&a_key).expect("file id for a.ts");
  let v_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("definition for v");
  let v_ty = program.type_of_def_interned(v_def);
  println!("v type {}", program.display_type(v_ty));
  assert_ne!(
    program.display_type(v_ty).to_string(),
    "unknown",
    "resolved type for v should not be unknown"
  );
  let offset = a_src.find("x;").expect("marker offset") as u32;
  let expr_at = program.expr_at(file_id, offset);
  println!("expr_at {expr_at:?}");
  let ty = program.type_at(file_id, offset).expect("type at v.x");
  println!("type at v.x {}", program.display_type(ty));
  let body = program.file_body(file_id);
  println!("file body: {body:?}");
  if let Some(body_id) = body.or(expr_at.map(|(b, _)| b)) {
    let res = program.check_body(body_id);
    if let Some(obj_ty) = res.expr_type(typecheck_ts::ExprId(0)) {
      println!("expr0 kind {:?}", program.interned_type_kind(obj_ty));
    }
    for (idx, span) in res.expr_spans().iter().enumerate() {
      if let Some(ty) = res.expr_type(typecheck_ts::ExprId(idx as u32)) {
        println!("{idx}: {span:?} -> {}", program.display_type(ty));
      }
    }
  }
  assert_eq!(program.display_type(ty).to_string(), "number");
}
