use diagnostics::{FileId, TextRange};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::sync::Arc;

use crate::js::{bind_js, TopLevelMode};
use crate::ts;

const MAX_DEPTH: usize = 4;
const MAX_STMTS_PER_BLOCK: usize = 4;
const MAX_BYTES_PER_STRING: usize = 24;

struct ByteCursor<'a> {
  data: &'a [u8],
  offset: usize,
}

impl<'a> ByteCursor<'a> {
  fn new(data: &'a [u8]) -> Self {
    Self { data, offset: 0 }
  }

  fn next_u8(&mut self) -> u8 {
    let b = self.data.get(self.offset).copied().unwrap_or(0);
    self.offset = self.offset.saturating_add(1);
    b
  }

  fn next_u32(&mut self) -> u32 {
    u32::from_le_bytes([
      self.next_u8(),
      self.next_u8(),
      self.next_u8(),
      self.next_u8(),
    ])
  }

  fn next_usize(&mut self, max_exclusive: usize) -> usize {
    if max_exclusive == 0 {
      return 0;
    }
    (self.next_u8() as usize) % max_exclusive
  }

  fn next_bool(&mut self) -> bool {
    self.next_u8() & 1 == 1
  }

  fn take_bytes(&mut self, max_len: usize) -> &'a [u8] {
    let len = self.next_usize(max_len + 1);
    let end = self.offset.saturating_add(len).min(self.data.len());
    let slice = &self.data[self.offset.min(self.data.len())..end];
    self.offset = end;
    slice
  }
}

fn escape_bytes_as_js_string(bytes: &[u8]) -> String {
  let mut out = String::new();
  for b in bytes {
    use std::fmt::Write;
    let _ = write!(&mut out, "\\x{b:02x}");
  }
  out
}

fn ident(cursor: &mut ByteCursor<'_>, prefix: &str) -> String {
  let len = cursor.next_usize(6) + 1;
  let mut out = String::with_capacity(prefix.len() + len);
  out.push_str(prefix);
  for _ in 0..len {
    let c = b'a' + (cursor.next_u8() % 26);
    out.push(c as char);
  }
  out
}

struct SpanCursor {
  next: u32,
}

impl SpanCursor {
  fn new() -> Self {
    Self { next: 0 }
  }

  fn next_range(&mut self, cursor: &mut ByteCursor<'_>) -> TextRange {
    let start = self.next;
    let len = (cursor.next_u8() % 16).saturating_add(1) as u32;
    let end = start.saturating_add(len);
    self.next = end.saturating_add(1);
    TextRange::new(start, end)
  }
}

fn gen_block(cursor: &mut ByteCursor<'_>, depth: usize) -> String {
  let stmt_count = cursor.next_usize(MAX_STMTS_PER_BLOCK) + 1;
  let mut out = String::new();
  for _ in 0..stmt_count {
    out.push_str(&gen_stmt(cursor, depth));
  }
  out
}

fn gen_stmt(cursor: &mut ByteCursor<'_>, depth: usize) -> String {
  if depth == 0 {
    let name = ident(cursor, "v");
    let value = cursor.next_usize(8);
    return format!("var {name} = {value};");
  }

  match cursor.next_usize(7) {
    // Nested block scope.
    0 => format!("{{ {} }}", gen_block(cursor, depth - 1)),
    // Function declaration.
    1 => {
      let name = ident(cursor, "f");
      format!("function {name}() {{ {} }}", gen_block(cursor, depth - 1))
    }
    // Arrow function + block.
    2 => {
      let name = ident(cursor, "a");
      format!(
        "const {name} = () => {{ {} }};",
        gen_block(cursor, depth - 1)
      )
    }
    // `with` introduces dynamic scope.
    3 => format!("with ({{}}) {{ {} }}", gen_block(cursor, depth - 1)),
    // Direct eval call also introduces dynamic scope.
    4 => {
      let payload = escape_bytes_as_js_string(cursor.take_bytes(MAX_BYTES_PER_STRING));
      format!("eval(\"{payload}\");")
    }
    // Block scoped bindings.
    5 => {
      let name = ident(cursor, "l");
      let value = cursor.next_usize(16);
      if cursor.next_bool() {
        format!("let {name} = {value};")
      } else {
        format!("const {name} = {value};")
      }
    }
    // `try`/`catch` introduces additional scopes.
    _ => {
      let name = ident(cursor, "e");
      format!(
        "try {{ {} }} catch ({name}) {{ {} }}",
        gen_block(cursor, depth - 1),
        gen_block(cursor, depth - 1)
      )
    }
  }
}

/// Fuzz entry point that generates syntactically valid JavaScript with
/// scoping constructs (functions, blocks, `with`, `eval`) and runs the JS binder
/// without panicking.
#[doc(hidden)]
pub fn fuzz_js_binder(data: &[u8]) {
  let mut cursor = ByteCursor::new(data);
  let mut source = gen_block(&mut cursor, MAX_DEPTH);
  // Ensure the resulting script parses even if the generator emits only
  // declarations (e.g. function declarations).
  source.push_str(";");

  let opts = ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  };
  let Ok(mut ast) = parse_with_options(&source, opts) else {
    return;
  };
  let _ = bind_js(&mut ast, TopLevelMode::Global, FileId(0));
}

const MAX_TS_NAMES: usize = 6;
const MAX_TS_SPECIFIERS: usize = 4;
const MAX_TS_DECLS: usize = 16;
const MAX_TS_IMPORTS: usize = 6;
const MAX_TS_IMPORT_ITEMS: usize = 4;
const MAX_TS_EXPORTS: usize = 8;
const MAX_TS_AMBIENT_MODULES: usize = 4;
const MAX_TS_AMBIENT_DEPTH: usize = 2;

fn gen_module_spec(cursor: &mut ByteCursor<'_>) -> String {
  let base = ident(cursor, "m");
  match cursor.next_usize(3) {
    0 => base,
    1 => format!("./{base}"),
    _ => format!("/{base}"),
  }
}

fn maybe_pick_name(cursor: &mut ByteCursor<'_>, pool: &[String], prefix: &str) -> String {
  if !pool.is_empty() && cursor.next_bool() {
    pool[cursor.next_usize(pool.len())].clone()
  } else {
    ident(cursor, prefix)
  }
}

fn gen_decl_kind(cursor: &mut ByteCursor<'_>) -> ts::DeclKind {
  match cursor.next_usize(7) {
    0 => ts::DeclKind::Function,
    1 => ts::DeclKind::Class,
    2 => ts::DeclKind::Var,
    3 => ts::DeclKind::Interface,
    4 => ts::DeclKind::TypeAlias,
    5 => ts::DeclKind::Enum,
    _ => ts::DeclKind::Namespace,
  }
}

fn gen_exported(cursor: &mut ByteCursor<'_>) -> ts::Exported {
  match cursor.next_usize(3) {
    0 => ts::Exported::No,
    1 => ts::Exported::Named,
    _ => ts::Exported::Default,
  }
}

fn gen_decl(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
  allow_import_binding: bool,
) -> ts::Decl {
  let kind = if allow_import_binding && cursor.next_usize(12) == 0 {
    ts::DeclKind::ImportBinding
  } else {
    gen_decl_kind(cursor)
  };
  ts::Decl {
    def_id: ts::DefId(cursor.next_u32()),
    name: maybe_pick_name(cursor, names, "d"),
    kind,
    is_ambient: cursor.next_bool(),
    is_global: cursor.next_bool(),
    exported: gen_exported(cursor),
    span: spans.next_range(cursor),
  }
}

fn gen_import(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
  specifiers: &[String],
) -> ts::Import {
  let specifier = maybe_pick_name(cursor, specifiers, "m");
  let specifier_span = spans.next_range(cursor);
  let is_type_only = cursor.next_bool();

  let default = if cursor.next_bool() {
    Some(ts::ImportDefault {
      local: maybe_pick_name(cursor, names, "i"),
      local_span: spans.next_range(cursor),
      is_type_only: cursor.next_bool(),
    })
  } else {
    None
  };

  let namespace = if cursor.next_bool() {
    Some(ts::ImportNamespace {
      local: maybe_pick_name(cursor, names, "ns"),
      local_span: spans.next_range(cursor),
      is_type_only: cursor.next_bool(),
    })
  } else {
    None
  };

  let named_count = cursor.next_usize(MAX_TS_IMPORT_ITEMS + 1);
  let mut named = Vec::new();
  for _ in 0..named_count {
    named.push(ts::ImportNamed {
      imported: maybe_pick_name(cursor, names, "im"),
      local: maybe_pick_name(cursor, names, "il"),
      is_type_only: cursor.next_bool(),
      imported_span: spans.next_range(cursor),
      local_span: spans.next_range(cursor),
    });
  }

  ts::Import {
    specifier,
    specifier_span,
    default,
    namespace,
    named,
    is_type_only,
  }
}

fn gen_type_import(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  specifiers: &[String],
) -> ts::TypeImport {
  ts::TypeImport {
    specifier: maybe_pick_name(cursor, specifiers, "m"),
    specifier_span: spans.next_range(cursor),
  }
}

fn gen_import_equals(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
  specifiers: &[String],
) -> ts::ImportEquals {
  let local = maybe_pick_name(cursor, names, "ie");
  let local_span = spans.next_range(cursor);
  let is_exported = cursor.next_bool();
  let target = if cursor.next_bool() {
    ts::ImportEqualsTarget::Require {
      specifier: maybe_pick_name(cursor, specifiers, "m"),
      specifier_span: spans.next_range(cursor),
    }
  } else {
    let count = cursor.next_usize(3) + 1;
    let mut path = Vec::new();
    for _ in 0..count {
      path.push(maybe_pick_name(cursor, names, "p"));
    }
    ts::ImportEqualsTarget::EntityName {
      path,
      span: spans.next_range(cursor),
    }
  };
  ts::ImportEquals {
    local,
    local_span,
    target,
    is_exported,
  }
}

fn gen_export_specifier(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
) -> ts::ExportSpecifier {
  let local = maybe_pick_name(cursor, names, "e");
  let local_span = spans.next_range(cursor);
  let exported = if cursor.next_bool() {
    Some(maybe_pick_name(cursor, names, "ex"))
  } else {
    None
  };
  let exported_span = exported.as_ref().map(|_| spans.next_range(cursor));
  ts::ExportSpecifier {
    local,
    exported,
    local_span,
    exported_span,
  }
}

fn gen_export(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
  specifiers: &[String],
) -> ts::Export {
  match cursor.next_usize(3) {
    0 => {
      let is_type_only = cursor.next_bool();
      let has_spec = cursor.next_bool();
      let specifier = if has_spec {
        Some(maybe_pick_name(cursor, specifiers, "m"))
      } else {
        None
      };
      let specifier_span = specifier.as_ref().map(|_| spans.next_range(cursor));
      let item_count = cursor.next_usize(MAX_TS_IMPORT_ITEMS + 1);
      let mut items = Vec::new();
      for _ in 0..item_count {
        items.push(gen_export_specifier(cursor, spans, names));
      }
      ts::Export::Named(ts::NamedExport {
        specifier,
        specifier_span,
        items,
        is_type_only,
      })
    }
    1 => {
      let specifier = maybe_pick_name(cursor, specifiers, "m");
      let specifier_span = spans.next_range(cursor);
      let alias = if cursor.next_bool() {
        Some(maybe_pick_name(cursor, names, "a"))
      } else {
        None
      };
      let alias_span = alias.as_ref().map(|_| spans.next_range(cursor));
      ts::Export::All(ts::ExportAll {
        specifier,
        is_type_only: cursor.next_bool(),
        specifier_span,
        alias,
        alias_span,
      })
    }
    _ => {
      let span = spans.next_range(cursor);
      let expr_span = spans.next_range(cursor);
      let path = if cursor.next_bool() {
        let count = cursor.next_usize(3) + 1;
        let mut path = Vec::new();
        for _ in 0..count {
          path.push(maybe_pick_name(cursor, names, "p"));
        }
        Some(path)
      } else {
        None
      };
      ts::Export::ExportAssignment {
        path,
        expr_span,
        span,
      }
    }
  }
}

fn gen_export_as_namespace(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
) -> ts::ExportAsNamespace {
  ts::ExportAsNamespace {
    name: maybe_pick_name(cursor, names, "ns"),
    span: spans.next_range(cursor),
  }
}

fn gen_ambient_module(
  cursor: &mut ByteCursor<'_>,
  spans: &mut SpanCursor,
  names: &[String],
  specifiers: &[String],
  depth: usize,
) -> ts::AmbientModule {
  let name = maybe_pick_name(cursor, specifiers, "m");
  let name_span = spans.next_range(cursor);

  let decl_count = cursor.next_usize(MAX_TS_DECLS.min(8) + 1);
  let mut decls = Vec::new();
  for _ in 0..decl_count {
    let mut decl = gen_decl(cursor, spans, names, true);
    // Ambient module declarations default to `declare`, but still allow callers to
    // toggle flags via the generator.
    decl.is_ambient = true;
    decl.exported = ts::Exported::No;
    decls.push(decl);
  }

  let import_count = cursor.next_usize(MAX_TS_IMPORTS.min(3) + 1);
  let mut imports = Vec::new();
  for _ in 0..import_count {
    imports.push(gen_import(cursor, spans, names, specifiers));
  }

  let type_import_count = cursor.next_usize(2);
  let mut type_imports = Vec::new();
  for _ in 0..type_import_count {
    type_imports.push(gen_type_import(cursor, spans, specifiers));
  }

  let import_equals_count = cursor.next_usize(2);
  let mut import_equals = Vec::new();
  for _ in 0..import_equals_count {
    import_equals.push(gen_import_equals(cursor, spans, names, specifiers));
  }

  let export_count = cursor.next_usize(MAX_TS_EXPORTS.min(4) + 1);
  let mut exports = Vec::new();
  for _ in 0..export_count {
    exports.push(gen_export(cursor, spans, names, specifiers));
  }

  let export_as_namespace_count = cursor.next_usize(2);
  let mut export_as_namespace = Vec::new();
  for _ in 0..export_as_namespace_count {
    export_as_namespace.push(gen_export_as_namespace(cursor, spans, names));
  }

  let ambient_modules = if depth > 0 {
    let nested_count = cursor.next_usize(MAX_TS_AMBIENT_MODULES.min(2) + 1);
    let mut nested = Vec::new();
    for _ in 0..nested_count {
      nested.push(gen_ambient_module(
        cursor,
        spans,
        names,
        specifiers,
        depth - 1,
      ));
    }
    nested
  } else {
    Vec::new()
  };

  ts::AmbientModule {
    name,
    name_span,
    decls,
    imports,
    type_imports,
    import_equals,
    exports,
    export_as_namespace,
    ambient_modules,
  }
}

fn gen_ts_hir_file(cursor: &mut ByteCursor<'_>, file_id: FileId) -> ts::HirFile {
  let mut spans = SpanCursor::new();

  let module_kind = if cursor.next_bool() {
    ts::ModuleKind::Module
  } else {
    ts::ModuleKind::Script
  };
  let file_kind = if cursor.next_bool() {
    ts::FileKind::Ts
  } else {
    ts::FileKind::Dts
  };

  let name_count = cursor.next_usize(MAX_TS_NAMES) + 1;
  let mut names = Vec::new();
  for _ in 0..name_count {
    names.push(ident(cursor, "n"));
  }

  let spec_count = cursor.next_usize(MAX_TS_SPECIFIERS) + 1;
  let mut specifiers = Vec::new();
  for _ in 0..spec_count {
    specifiers.push(gen_module_spec(cursor));
  }

  let decl_count = cursor.next_usize(MAX_TS_DECLS + 1);
  let mut decls = Vec::new();
  for _ in 0..decl_count {
    decls.push(gen_decl(cursor, &mut spans, &names, false));
  }

  let type_import_count = cursor.next_usize(3);
  let mut type_imports = Vec::new();
  for _ in 0..type_import_count {
    type_imports.push(gen_type_import(cursor, &mut spans, &specifiers));
  }

  let import_count = cursor.next_usize(MAX_TS_IMPORTS + 1);
  let mut imports = Vec::new();
  for _ in 0..import_count {
    imports.push(gen_import(cursor, &mut spans, &names, &specifiers));
  }

  let import_equals_count = cursor.next_usize(4);
  let mut import_equals = Vec::new();
  for _ in 0..import_equals_count {
    import_equals.push(gen_import_equals(cursor, &mut spans, &names, &specifiers));
  }

  let export_count = cursor.next_usize(MAX_TS_EXPORTS + 1);
  let mut exports = Vec::new();
  for _ in 0..export_count {
    exports.push(gen_export(cursor, &mut spans, &names, &specifiers));
  }

  let export_as_namespace_count = cursor.next_usize(3);
  let mut export_as_namespace = Vec::new();
  for _ in 0..export_as_namespace_count {
    export_as_namespace.push(gen_export_as_namespace(cursor, &mut spans, &names));
  }

  let ambient_count = cursor.next_usize(MAX_TS_AMBIENT_MODULES + 1);
  let mut ambient_modules = Vec::new();
  for _ in 0..ambient_count {
    ambient_modules.push(gen_ambient_module(
      cursor,
      &mut spans,
      &names,
      &specifiers,
      MAX_TS_AMBIENT_DEPTH,
    ));
  }

  ts::HirFile {
    file_id,
    module_kind,
    file_kind,
    decls,
    imports,
    type_imports,
    import_equals,
    exports,
    export_as_namespace,
    ambient_modules,
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExportEntrySnapshot {
  name: String,
  namespaces: u8,
  value: Option<u64>,
  ty: Option<u64>,
  namespace: Option<u64>,
}

fn snapshot_export_map(map: &ts::ExportMap, symbols: &ts::SymbolTable) -> Vec<ExportEntrySnapshot> {
  map
    .iter()
    .map(|(name, group)| ExportEntrySnapshot {
      name: name.clone(),
      namespaces: group.namespaces(symbols).bits(),
      value: group
        .symbol_for(ts::Namespace::VALUE, symbols)
        .map(|s| s.raw()),
      ty: group
        .symbol_for(ts::Namespace::TYPE, symbols)
        .map(|s| s.raw()),
      namespace: group
        .symbol_for(ts::Namespace::NAMESPACE, symbols)
        .map(|s| s.raw()),
    })
    .collect()
}

fn snapshot_exports(
  sem: &ts::TsProgramSemantics,
  root: FileId,
) -> Vec<(String, Vec<ExportEntrySnapshot>)> {
  let symbols = sem.symbols();
  let mut out = Vec::new();

  let root_map = sem
    .exports_of_opt(root)
    .map(|m| snapshot_export_map(m, symbols));
  out.push(("module".to_string(), root_map.unwrap_or_default()));

  for (name, exports) in sem.ambient_module_exports().iter() {
    out.push((
      format!("ambient:{name}"),
      snapshot_export_map(exports, symbols),
    ));
  }

  out
}

/// Fuzz entry point that generates synthetic `ts::HirFile` inputs heavy on
/// declaration merging and export computation. Runs the TS program binder twice
/// to assert deterministic exports and symbol table allocation.
#[doc(hidden)]
pub fn fuzz_ts_binder(data: &[u8]) {
  let mut cursor = ByteCursor::new(data);
  let file_id = FileId(0);
  let hir = Arc::new(gen_ts_hir_file(&mut cursor, file_id));

  struct NullResolver;

  impl ts::Resolver for NullResolver {
    fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
      None
    }
  }

  let resolver = NullResolver;
  let bind = |hir: Arc<ts::HirFile>| {
    ts::bind_ts_program(&[file_id], &resolver, move |id| {
      if id == file_id {
        hir.clone()
      } else {
        Arc::new(ts::HirFile::module(id))
      }
    })
    .0
  };

  let sem1 = bind(hir.clone());
  let sem2 = bind(hir);

  assert_eq!(
    snapshot_exports(&sem1, file_id),
    snapshot_exports(&sem2, file_id)
  );
  assert_eq!(sem1.symbols.symbols, sem2.symbols.symbols);
  assert_eq!(sem1.symbols.decls, sem2.symbols.decls);
  assert_eq!(sem1.def_to_symbol, sem2.def_to_symbol);
}
