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
fn debug_excess_props_call() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("main.ts");
  let fixture = format!(
    "{}/tests/litmus/excess_props/main.ts",
    env!("CARGO_MANIFEST_DIR")
  );
  let source = std::fs::read_to_string(fixture).expect("read fixture");
  host.insert(key.clone(), source.clone());

  let program = Program::new(host, vec![key.clone()]);
  let diags = program.check();
  println!("diagnostics: {diags:?}");
  if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
    let test_store = types_ts_interned::TypeStore::with_options(
      (&typecheck_ts::lib_support::CompilerOptions::default()).into(),
    );
    let prim = test_store.primitive_ids();
    let union = test_store.union(vec![prim.number, prim.string]);
    let relate =
      types_ts_interned::RelateCtx::new(std::sync::Arc::clone(&test_store), test_store.options());
    println!(
      "assignable number->union {} union->number {}",
      relate.is_assignable(prim.number, union),
      relate.is_assignable(union, prim.number)
    );
  }

  let file_id = program.file_id(&key).expect("file id");
  for def in program.definitions_in_file(file_id) {
    let name = program
      .def_name(def)
      .unwrap_or_else(|| "<anon>".to_string());
    let ty = program.display_type(program.type_of_def(def));
    println!("def {def:?} name {name} type {ty}");
  }

  if let Some(body) = program.file_body(file_id) {
    let res = program.check_body(body);
    for (idx, span) in res.expr_spans().iter().enumerate() {
      if let Some(ty) = res.expr_type(typecheck_ts::ExprId(idx as u32)) {
        println!("{idx}: {span:?} -> {}", program.display_type(ty));
      }
    }
  }
}

#[test]
#[ignore]
fn debug_narrowing_patterns_fixture() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("main.ts");
  let fixture = format!(
    "{}/tests/litmus/narrowing_patterns/main.ts",
    env!("CARGO_MANIFEST_DIR")
  );
  let source = std::fs::read_to_string(fixture).expect("read fixture");
  host.insert(key.clone(), source.clone());

  let program = Program::new(host, vec![key.clone()]);
  let diags = program.check();
  println!("diagnostics: {diags:?}");

  let file_id = program.file_id(&key).expect("file id");
  for def in program.definitions_in_file(file_id) {
    let name = program
      .def_name(def)
      .unwrap_or_else(|| "<anon>".to_string());
    if name == "assertNumber"
      || name == "isString"
      || name == "onlyObjects"
      || name == "useAssert"
      || name == "guardUse"
    {
      let ty = program.type_of_def(def);
      let sigs = program.call_signatures(ty);
      let ret_sigs: Vec<_> = sigs
        .iter()
        .map(|sig| program.display_type(sig.signature.ret).to_string())
        .collect();
      println!(
        "def {name} type {} signatures {ret_sigs:?}",
        program.display_type(ty)
      );
      for sig in sigs.iter() {
        println!(
          "    ret kind for {name}: {:?}",
          program.interned_type_kind(sig.signature.ret)
        );
      }
      if let Some(body) = program.body_of_def(def) {
        let res = program.check_body(body);
        println!("  expr spans/types for {name}:");
        for (idx, span) in res.expr_spans().iter().enumerate() {
          if let Some(ty) = res.expr_type(typecheck_ts::ExprId(idx as u32)) {
            println!("    {idx}: {span:?} -> {}", program.display_type(ty));
          }
        }
        println!("  pat spans/types for {name}:");
        for (idx, span) in res.pat_spans().iter().enumerate() {
          if let Some(ty) = res.pat_type(typecheck_ts::PatId(idx as u32)) {
            println!("    {idx}: {span:?} -> {}", program.display_type(ty));
          }
        }
        if !res.return_types().is_empty() {
          println!(
            "  return types: {:?}",
            res
              .return_types()
              .iter()
              .map(|t| program.display_type(*t).to_string())
              .collect::<Vec<_>>()
          );
        }
      }
    }
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
fn debug_import_overload_typeof() {
  let mut host = MemoryHost::default();
  let key_math = FileKey::new("math.ts");
  let key_use = FileKey::new("use.ts");
  host.insert(
    key_math.clone(),
    "export function overload(value: string): string;\n\
     export function overload(value: number): number;\n\
     export function overload(value: string | number) { return value; }",
  );
  host.insert(
    key_use.clone(),
    "import { overload } from \"./math\";\n\
     type Over = typeof overload;\n\
     const fn: Over = overload;\n\
     export const viaString = fn(\"hi\");\n\
     export const viaNumber = fn(2);",
  );
  host.link(key_use.clone(), "./math", key_math.clone());

  let program = Program::new(host, vec![key_use.clone()]);
  let diagnostics = program.check();
  println!("diagnostics: {diagnostics:?}");

  let math_id = program.file_id(&key_math).unwrap();
  let math_exports = program.exports_of(math_id);
  for (name, entry) in math_exports.iter() {
    println!(
      "math export {name}: def {:?} type {:?}",
      entry.def,
      entry.type_id.map(|t| program.display_type(t).to_string())
    );
  }
  let use_id = program.file_id(&key_use).unwrap();
  for def in program.definitions_in_file(use_id) {
    let name = program
      .def_name(def)
      .unwrap_or_else(|| "<anon>".to_string());
    let ty = program.display_type(program.type_of_def(def)).to_string();
    println!("def {def:?} name {name} type {ty}");
    if name == "fn" || name == "Over" || name == "overload" {
      let sigs = program.call_signatures(program.type_of_def(def));
      println!(
        "  call signatures for {name}: {}",
        sigs
          .iter()
          .map(|s| program.display_type(s.signature.ret).to_string())
          .collect::<Vec<_>>()
          .join(", ")
      );
    }
  }
  let exports = program.exports_of(use_id);
  for (name, entry) in exports.iter() {
    println!(
      "export {name}: def {:?} type {:?}",
      entry.def,
      entry.type_id.map(|t| program.display_type(t).to_string())
    );
  }
  if let Some(body) = program.file_body(use_id) {
    let res = program.check_body(body);
    for (idx, span) in res.expr_spans().iter().enumerate() {
      if let Some(ty) = res.expr_type(typecheck_ts::ExprId(idx as u32)) {
        println!("expr {idx}: {span:?} -> {}", program.display_type(ty));
      }
    }
  }
}

#[test]
#[ignore]
fn debug_doc_example() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("file0.ts");
  host.insert(
    key.clone(),
    "export function add(a: number, b: number) { return a + b; }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diags = program.check();
  println!("diagnostics: {diags:?}");

  let file_id = program.file_id(&key).unwrap();
  let exports = program.exports_of(file_id);
  println!("exports: {:?}", exports.keys().collect::<Vec<_>>());
  let add_def = exports.get("add").and_then(|e| e.def).unwrap();
  println!(
    "add def {:?} body {:?} type {}",
    add_def,
    program.body_of_def(add_def),
    program.display_type(program.type_of_def(add_def))
  );
  if let Some(body) = program.body_of_def(add_def) {
    let res = program.check_body(body);
    for (idx, span) in res.expr_spans().iter().enumerate() {
      let ty = res.expr_type(typecheck_ts::ExprId(idx as u32)).unwrap();
      println!("expr {idx}: {span:?} -> {}", program.display_type(ty));
    }
    for (idx, span) in res.pat_spans().iter().enumerate() {
      if let Some(ty) = res.pat_type(typecheck_ts::PatId(idx as u32)) {
        println!("pat {idx}: {span:?} -> {}", program.display_type(ty));
      }
    }
  }

  let parsed =
    parse_js::parse("export function add(a: number, b: number) { return a + b; }").expect("parse");
  if let Some(func_node) = parsed.stx.body.first() {
    if let parse_js::ast::stmt::Stmt::FunctionDecl(func_decl) = func_node.stx.as_ref() {
      let function = &func_decl.stx.function;
      if let Some(parse_js::ast::func::FuncBody::Block(block)) = &function.stx.body {
        if let Some(ret_node) = block.first() {
          if let parse_js::ast::stmt::Stmt::Return(ret) = ret_node.stx.as_ref() {
            if let Some(expr_node) = ret.stx.value.as_ref() {
              if let parse_js::ast::expr::Expr::Binary(bin) = expr_node.stx.as_ref() {
                let (left_range, _) = bin.stx.left.loc.to_diagnostics_range_with_note();
                let (right_range, _) = bin.stx.right.loc.to_diagnostics_range_with_note();
                let (bin_range, _) = bin.loc.to_diagnostics_range_with_note();
                println!("AST left range: {:?}", left_range);
                println!("AST right range: {:?}", right_range);
                println!("AST bin range: {:?}", bin_range);
              }
            }
          }
        }
      }
    }
  }
}
