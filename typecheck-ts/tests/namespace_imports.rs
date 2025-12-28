use typecheck_ts::{ExprId, FileKey, MemoryHost, Program};

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
  let m_id = program.file_id(&m_key).expect("m id");
  let re_id = program.file_id(&re_key).expect("re id");
  println!("exports m: {:?}", program.exports_of(m_id));
  println!("exports re: {:?}", program.exports_of(re_id));
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&a_key).expect("file id for a.ts");
  let m_id = program.file_id(&FileKey::new("m.ts")).expect("m id");
  println!(
    "defs in m: {:?}",
    program
      .definitions_in_file(m_id)
      .iter()
      .map(|d| (d, program.def_name(*d)))
      .collect::<Vec<_>>()
  );
  println!(
    "all defs: {:?}",
    program
      .files()
      .into_iter()
      .map(|id| {
        (
          program.file_key(id),
          program
            .definitions_in_file(id)
            .into_iter()
            .map(|d| (d, program.def_name(d)))
            .collect::<Vec<_>>(),
        )
      })
      .collect::<Vec<_>>()
  );
  println!(
    "defs in a: {:?}",
    program
      .definitions_in_file(file_id)
      .iter()
      .map(|d| (d, program.def_name(*d)))
      .collect::<Vec<_>>()
  );
  if let Some(ns_def) = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("NS"))
  {
    println!(
      "NS type {}",
      program
        .display_type(program.type_of_def(ns_def))
        .to_string()
    );
  }
  let exports_m = program.exports_of(m_id);
  println!(
    "exports in m: {:?}",
    exports_m
      .iter()
      .map(|(name, entry)| {
        (
          name.clone(),
          entry.type_id.map(|ty| program.display_type(ty).to_string()),
        )
      })
      .collect::<Vec<_>>()
  );
  let v_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("definition for v");
  let v_ty = program.type_of_def_interned(v_def);
  println!("v ty: {}", program.display_type(v_ty));
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
  println!("diagnostics: {diagnostics:?}");
  let m_id = program.file_id(&FileKey::new("m.ts")).expect("m id");
  println!("exports m: {:?}", program.exports_of(m_id));
  for def in program.definitions_in_file(m_id) {
    println!(
      "m def {:?} {}",
      program.def_name(def),
      program.display_type(program.type_of_def_interned(def))
    );
    println!("  kind {:?}", program.interned_type_kind(program.type_of_def_interned(def)));
    println!(
      "  props {:?}",
      program
        .properties_of(program.type_of_def_interned(def))
        .iter()
        .map(|p| (p.key.clone(), program.display_type(p.ty).to_string()))
        .collect::<Vec<_>>()
    );
  }
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&a_key).expect("file id for a.ts");
  let v_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("definition for v");
  let v_ty = program.type_of_def_interned(v_def);
  println!("v ty: {}", program.display_type(v_ty));
  assert_ne!(
    program.display_type(v_ty).to_string(),
    "unknown",
    "resolved type for v should not be unknown"
  );
  let offset = a_src.find("x;").expect("marker offset") as u32;
  if let Some((body, expr)) = program.expr_at(file_id, offset) {
    let res = program.check_body(body);
    if let Some(t0) = res.expr_type(ExprId(0)) {
      println!("expr0 kind {:?}", program.interned_type_kind(t0));
      if let types_ts_interned::TypeKind::Ref { def, args: _ } = program.interned_type_kind(t0) {
        println!("expr0 def {:?}", program.def_name(def));
        println!(
          "expr0 def span {:?} type {}",
          program.span_of_def(def),
          program.display_type(program.type_of_def_interned(def))
        );
      }
    }
    println!(
      "expr_at -> {:?} span {:?} type {}",
      expr,
      res.expr_span(expr),
      res
        .expr_type(expr)
        .map(|ty| program.display_type(ty).to_string())
        .unwrap_or_else(|| "<none>".to_string())
    );
    for (idx, span) in res.expr_spans().iter().enumerate() {
      println!(
        "  {idx}: {:?} -> {}",
        span,
        res
          .expr_type(typecheck_ts::ExprId(idx as u32))
          .map(|ty| program.display_type(ty).to_string())
          .unwrap_or_else(|| "<none>".to_string())
      );
    }
  }
  let ty = program.type_at(file_id, offset).expect("type at v.x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
