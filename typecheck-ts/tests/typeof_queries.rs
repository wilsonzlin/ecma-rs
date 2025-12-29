use std::sync::Arc;

use hir_js::{lower_from_source_with_kind, FileKind as HirFileKind};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn typeof_queries_in_libs_resolve_value_types() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("entry.ts");
  let source = "const t = window.document.title;";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let lib_source = include_str!("../fixtures/libs/lib.dom.d.ts");
  let lowered = lower_from_source_with_kind(HirFileKind::Dts, lib_source).expect("lower lib");
  for def in lowered.defs.iter() {
    let name = lowered.names.resolve(def.name).unwrap_or_default();
    eprintln!("lib def {name} type_info={}", def.type_info.is_some());
  }

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id for entry");
  let offset = source.find("title").expect("title property offset") as u32;
  let ty = program
    .type_at(file_id, offset)
    .expect("type of window.document.title");
  let debug = program.display_type(ty).to_string();
  eprintln!("type_at(title) -> {debug}");
  let globals = program.global_bindings();
  if let Some(binding) = globals.get("window") {
    eprintln!("global window binding: {:?}", binding);
    if let Some(ty) = binding.type_id {
      eprintln!("global window type {}", program.display_type(ty));
    }
    if let Some(def) = binding.def {
      eprintln!(
        "window def type {}",
        program.display_type(program.type_of_def(def))
      );
      eprintln!(
        "window def interned type {}",
        program.display_type(program.type_of_def_interned(def))
      );
      let win_props = program.properties_of(program.type_of_def_interned(def));
      for prop in win_props {
        eprintln!(
          "window prop {:?}: {}",
          prop.key,
          program.display_type(prop.ty)
        );
      }
    }
  }
  if let Some(binding) = globals.get("Window") {
    eprintln!("global Window binding: {:?}", binding);
    if let Some(ty) = binding.type_id {
      eprintln!("global Window type {}", program.display_type(ty));
    }
    if let Some(def) = binding.def {
      eprintln!(
        "Window def type {}",
        program.display_type(program.type_of_def(def))
      );
    }
  }
  if let Some(binding) = globals.get("document") {
    eprintln!("global document binding: {:?}", binding);
    if let Some(ty) = binding.type_id {
      eprintln!("global document type {}", program.display_type(ty));
    }
    if let Some(def) = binding.def {
      eprintln!(
        "document def type {}",
        program.display_type(program.type_of_def(def))
      );
    }
  }
  for file in program.reachable_files() {
    for def in program.definitions_in_file(file) {
      if let Some(name) = program.def_name(def) {
        if name == "window" || name == "document" || name == "Window" || name == "Document" {
          eprintln!(
            "def {name} type {}",
            program.display_type(program.type_of_def(def))
          );
        }
      }
    }
  }
  if let Some((body, expr)) = program.expr_at(file_id, offset) {
    let result = program.check_body(body);
    eprintln!(
      "expr_at {expr:?} span {:?} type {:?}",
      result.expr_span(expr),
      result
        .expr_type(expr)
        .map(|ty| program.display_type(ty).to_string())
    );
    for (idx, span) in result.expr_spans().iter().enumerate() {
      eprintln!(
        "{idx}: {:?} -> {}",
        span,
        result
          .expr_type(typecheck_ts::ExprId(idx as u32))
          .map(|ty| program.display_type(ty).to_string())
          .unwrap_or_else(|| "<none>".to_string())
      );
    }
  }
  assert_eq!(program.display_type(ty).to_string(), "string");
}
