use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn debug_namespace_defs() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("ns.ts");
  host.insert(
    key.clone(),
    "namespace foo { const bar = 1; }\nfunction foo() { return foo.bar; }\nexport { foo };",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  println!("diagnostics: {:?}", diagnostics);

  let file_id = program.file_id(&key).expect("file id");
  let defs = program.definitions_in_file(file_id);
  for &def in defs.iter() {
    let name = program.def_name(def).unwrap_or_default();
    let body = program.body_of_def(def);
    let span = program.def_span(def);
    println!("def {:?} name {name} body {:?} span {:?}", def, body, span);
  }

  let exports = program.exports_of(file_id);
  println!("exports: {:?}", exports.keys().collect::<Vec<_>>());
  if let Some(entry) = exports.get("foo") {
    println!("export foo -> def {:?} type {:?}", entry.def, entry.type_id);
  }

  if let Some(func_def) = defs
    .iter()
    .copied()
    .find(|d| program.body_of_def(*d).is_some())
  {
    let ty = program.type_of_def_interned(func_def);
    println!("func def {:?}", func_def);
    println!("func properties: {:?}", program.properties_of(ty));
    println!("func calls: {:?}", program.call_signatures(ty).len());
  }
}

#[test]
#[ignore]
fn print_namespace_hir() {
  let source =
    "export namespace Config { export const a = 1; }\nexport namespace Config { export const b = 2; }";
  let lowered = hir_js::lower_from_source(source).expect("lower");
  for def in lowered.defs.iter() {
    let name = lowered.names.resolve(def.name).unwrap_or_default();
    println!(
      "def {:?} kind {:?} name {} exported {} default {} body {:?} span {:?}",
      def.id, def.path.kind, name, def.is_exported, def.is_default_export, def.body, def.span
    );
  }
  println!("items: {:?}", lowered.hir.items);
  println!("bodies: {:?}", lowered.hir.bodies);
}

#[test]
#[ignore]
fn inspect_namespace_program_exports() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("ns_debug.ts");
  let source =
    "export namespace Config { export const a = 1; }\nexport namespace Config { export const b = 2; }";
  host.insert(file.clone(), source);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  println!("diags: {:?}", diagnostics);

  let file_id = program.file_id(&file).unwrap();
  let exports = program.exports_of(file_id);
  println!("exports: {:?}", exports.keys().collect::<Vec<_>>());
  for (name, entry) in exports.iter() {
    println!(
      "export {name}: def {:?} type {:?}",
      entry.def, entry.type_id
    );
  }
}

#[test]
#[ignore]
fn debug_symbol_shadowing() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("file.ts");
  let source = "const foo = 1; { const foo = 2; { const foo = 3; foo; } foo; } const again = foo;";
  host.insert(key.clone(), source);
  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).unwrap();
  for (idx, ch) in source.char_indices() {
    if ch == 'f' {
      let sym = program.symbol_at(file_id, idx as u32);
      println!("offset {idx} -> {:?}", sym);
    }
  }
}

#[test]
#[ignore]
fn debug_symbol_param() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("file.ts");
  let source = "function wrap(param: number) { const inner = param; return param; }";
  host.insert(key.clone(), source);
  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).unwrap();
  let defs = program.definitions_in_file(file_id);
  for def in defs {
    println!(
      "def {:?} name {:?} span {:?}",
      def,
      program.def_name(def),
      program.def_span(def)
    );
  }
  for (idx, ch) in source.char_indices() {
    if ch == 'p' {
      let sym = program.symbol_at(file_id, idx as u32);
      println!("offset {idx} -> {:?}", sym);
    }
  }
  println!("offset 19 -> {:?}", program.symbol_at(file_id, 19));
  let lowered = hir_js::lower_from_source(source).unwrap();
  println!(
    "span map def at 14 {:?}, 19 {:?}",
    lowered.hir.span_map.def_span_at_offset(14),
    lowered.hir.span_map.def_span_at_offset(19)
  );
}

#[test]
#[ignore]
fn debug_noop_void() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("noop.ts");
  host.insert(
    file.clone(),
    r#"
      function noop() {
        const value = 1;
      }
    "#,
  );

  let program = Program::new(host, vec![file.clone()]);
  let diags = program.check();
  println!("diagnostics: {diags:?}");
  let file_id = program.file_id(&file).unwrap();
  println!("program bodies: {:?}", program.bodies_in_file(file_id));
  for def in program.definitions_in_file(file_id) {
    let name = program.def_name(def).unwrap_or_default();
    let ty = program.display_type(program.type_of_def(def)).to_string();
    let body = program.body_of_def(def);
    println!("def {def:?} name {name} type {ty} body {body:?}");
    if let Some(body_id) = body {
      let res = program.check_body(body_id);
      println!(
        "  body expr types len {} return types {:?}",
        res.expr_spans().len(),
        res
          .return_types()
          .iter()
          .map(|t| program.display_type(*t).to_string())
          .collect::<Vec<_>>()
      );
    }
  }

  let source = r#"
      function noop() {
        const value = 1;
      }
    "#;
  let lowered = hir_js::lower_from_source(source).unwrap();
  let offset = source.find("value").unwrap() as u32;
  println!(
    "span map def at offset {offset}: {:?}",
    lowered.hir.span_map.def_span_at_offset(offset)
  );
  for def in lowered.defs.iter() {
    let name = lowered.names.resolve(def.name).unwrap_or_default();
    println!(
      "lowered def {:?} kind {:?} name {} span {:?} body {:?}",
      def.id, def.path.kind, name, def.span, def.body
    );
  }
}

#[test]
#[ignore]
fn debug_shadow_symbols() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("shadow.ts");
  let source = "const foo = 1; { const foo = 2; { const foo = 3; foo; } foo; } const again = foo;";
  host.insert(file.clone(), source);
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();
  let body = program.file_body(file_id).unwrap();
  let result = program.check_body(body);
  println!("expr spans: {:?}", result.expr_spans());
  println!("pat spans: {:?}", result.pat_spans());
  println!(
    "occurrences: {:?}",
    program.debug_symbol_occurrences(file_id)
  );
}

#[test]
#[ignore]
fn debug_contextual_object_literals() {
  let fixture = std::fs::read_to_string(
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("tests/litmus/contextual_object_literals/main.ts"),
  )
  .expect("fixture");
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::default();
  host.insert(key.clone(), fixture);
  let program = Program::new(host, vec![key.clone()]);
  let diags = program.check();
  println!("diagnostics: {diags:?}");
  let file_id = program.file_id(&key).unwrap();
  for def in program.definitions_in_file(file_id) {
    let name = program.def_name(def).unwrap_or_default();
    let ty = program.display_type(program.type_of_def(def)).to_string();
    println!("def {name} -> {ty}");
  }
}
