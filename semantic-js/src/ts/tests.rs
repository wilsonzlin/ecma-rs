use super::*;
use crate::assoc::{js, ts};
use crate::ts::from_hir_js::lower_to_ts_hir;
use crate::ts::locals::{bind_ts_locals, map_module_scope_locals_to_program};
use hir_js::hir::{ExprKind, FileKind as HirFileKind, TypeExprKind};
use hir_js::ids::{DefKind, ExprId, TypeExprId};
use hir_js::lower_file;
use parse_js::ast::node::NodeAssocData;
use parse_js::{parse, Dialect, ParseOptions, SourceType};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
use std::any::TypeId;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;
use std::thread;

#[derive(Clone)]
struct StaticResolver {
  map: HashMap<String, FileId>,
}

impl StaticResolver {
  fn new(map: HashMap<String, FileId>) -> Self {
    Self { map }
  }
}

impl Resolver for StaticResolver {
  fn resolve(&self, _from: FileId, specifier: &str) -> Option<FileId> {
    self.map.get(specifier).copied()
  }
}

fn mk_decl(def: u32, name: &str, kind: DeclKind, exported: Exported) -> Decl {
  Decl {
    def_id: DefId(def),
    name: name.to_string(),
    kind,
    is_ambient: false,
    is_global: false,
    exported,
    span: span(def),
  }
}

fn span(start: u32) -> TextRange {
  TextRange::new(start, start + 1)
}

fn positions(source: &str, needle: &str) -> Vec<u32> {
  let mut positions = Vec::new();
  let mut start = 0usize;
  while let Some(found) = source[start..].find(needle) {
    let pos = start + found;
    positions.push(pos as u32);
    start = pos + needle.len();
  }
  positions
}

fn export_snapshot(
  sem: &TsProgramSemantics,
  files: &[FileId],
) -> BTreeMap<FileId, Vec<(String, Namespace, SymbolId)>> {
  let mut out = BTreeMap::new();
  for file in files {
    let mut entries = Vec::new();
    for (name, group) in sem.exports_of(*file).iter() {
      for ns in [Namespace::VALUE, Namespace::TYPE, Namespace::NAMESPACE] {
        if let Some(sym) = group.symbol_for(ns, sem.symbols()) {
          entries.push((name.clone(), ns, sym));
        }
      }
    }
    entries.sort_by(|a, b| {
      a.0
        .cmp(&b.0)
        .then_with(|| a.1.bits().cmp(&b.1.bits()))
        .then_with(|| a.2.cmp(&b.2))
    });
    out.insert(*file, entries);
  }
  out
}

fn symbol_table_snapshot(table: &SymbolTable) -> (Vec<SymbolData>, Vec<DeclData>) {
  let mut symbols: Vec<_> = table.symbols.values().cloned().collect();
  symbols.sort_by_key(|s| s.id);

  let mut decls: Vec<_> = table.decls.values().cloned().collect();
  decls.sort_by_key(|d| d.id);

  (symbols, decls)
}

fn symbols_for_owner(table: &SymbolTable, owner: &SymbolOwner) -> Vec<SymbolData> {
  let mut symbols: Vec<_> = table
    .symbols
    .values()
    .filter(|s| &s.owner == owner)
    .cloned()
    .collect();
  symbols.sort_by_key(|s| s.id);
  symbols
}

fn decls_for_file(table: &SymbolTable, file: FileId) -> Vec<DeclData> {
  let mut decls: Vec<_> = table
    .decls
    .values()
    .filter(|d| d.file == file)
    .cloned()
    .collect();
  decls.sort_by_key(|d| d.id);
  decls
}

#[test]
fn ts_assoc_helpers_round_trip() {
  let mut assoc = NodeAssocData::default();
  let declared = ts::DeclaredSymbol(SymbolId(123));
  let resolved = SymbolId(456);

  assoc.set(declared);
  assoc.set(ts::ResolvedSymbol(Some(resolved)));

  assert_eq!(ts::declared_symbol(&assoc), Some(declared.0));
  assert_eq!(ts::resolved_symbol(&assoc), Some(resolved));
}

#[test]
fn ts_assoc_keys_do_not_overlap_js_accessors() {
  let mut assoc = NodeAssocData::default();
  assoc.set(ts::DeclaredSymbol(SymbolId(7)));
  assoc.set(ts::ResolvedSymbol(Some(SymbolId(9))));

  assert_eq!(js::declared_symbol(&assoc), None);
  assert_eq!(js::resolved_symbol(&assoc), None);
  assert_eq!(ts::declared_symbol(&assoc), Some(SymbolId(7)));
  assert_eq!(ts::resolved_symbol(&assoc), Some(SymbolId(9)));

  assert_ne!(
    TypeId::of::<ts::DeclaredSymbol>(),
    TypeId::of::<js::DeclaredSymbol>()
  );
  assert_ne!(
    TypeId::of::<ts::ResolvedSymbol>(),
    TypeId::of::<js::ResolvedSymbol>()
  );

  // Explicit type annotations ensure the accessors expose TS symbol IDs and
  // cannot be mistaken for JS ones at compile time.
  let _: Option<SymbolId> = ts::declared_symbol(&assoc);
  let _: Option<SymbolId> = ts::resolved_symbol(&assoc);
  let _: Option<crate::js::SymbolId> = js::declared_symbol(&assoc);
  let _: Option<crate::js::SymbolId> = js::resolved_symbol(&assoc);
}

#[test]
fn locals_resolve_object_literal_shorthand() {
  let source = "const x = 1; const obj = { x };";
  let mut ast = parse(source).expect("parse object literal shorthand");
  let locals = bind_ts_locals(&mut ast, FileId(0), true);

  let occs = positions(source, "x");
  assert!(
    occs.len() >= 2,
    "expected declaration and shorthand occurrences: {occs:?}"
  );
  let decl_offset = occs[0];
  let shorthand_offset = occs[1];

  let decl_symbol = locals
    .resolve_expr_at_offset(decl_offset)
    .map(|(_, id)| id)
    .expect("declaration should resolve");
  let shorthand_symbol = locals
    .resolve_expr_at_offset(shorthand_offset)
    .map(|(_, id)| id)
    .expect("shorthand should resolve");

  assert_eq!(
    decl_symbol, shorthand_symbol,
    "object literal shorthand should resolve to declared binding"
  );
}

#[test]
fn reexport_chain_uses_original_symbols() {
  let file_a = FileId(1);
  let file_b = FileId(2);
  let file_c = FileId(3);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "foo", DeclKind::Function, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.exports.push(Export::Named(NamedExport {
    specifier: Some("a".to_string()),
    specifier_span: Some(span(10)),
    items: vec![ExportSpecifier {
      local: "foo".to_string(),
      exported: None,
      local_span: span(11),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let mut c = HirFile::module(file_c);
  c.exports.push(Export::All(ExportAll {
    specifier: "b".to_string(),
    is_type_only: false,
    specifier_span: span(12),
    alias: None,
    alias_span: None,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
    file_c => Arc::new(c),
  };

  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
    "b".to_string() => file_b,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_c], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let symbols = semantics.symbols();
  let foo_a = semantics
    .exports_of(file_a)
    .get("foo")
    .unwrap()
    .symbol_for(Namespace::VALUE, symbols)
    .unwrap();
  let foo_b = semantics
    .exports_of(file_b)
    .get("foo")
    .unwrap()
    .symbol_for(Namespace::VALUE, symbols)
    .unwrap();
  let foo_c = semantics
    .exports_of(file_c)
    .get("foo")
    .unwrap()
    .symbol_for(Namespace::VALUE, symbols)
    .unwrap();

  assert_eq!(foo_a, foo_b);
  assert_eq!(foo_b, foo_c);
}

#[test]
fn export_all_as_namespace_adds_only_alias() {
  let file_a = FileId(400);
  let file_b = FileId(401);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "foo", DeclKind::Var, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.exports.push(Export::All(ExportAll {
    specifier: "a".to_string(),
    is_type_only: false,
    specifier_span: span(10),
    alias: Some("NS".to_string()),
    alias_span: Some(span(11)),
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };

  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let exports_b = semantics.exports_of(file_b);
  assert!(exports_b.contains_key("NS"));
  assert!(!exports_b.contains_key("foo"));

  let symbols = semantics.symbols();
  let ns_group = exports_b.get("NS").expect("namespace alias exported");
  let mask = ns_group.namespaces(symbols);
  assert!(mask.contains(Namespace::VALUE));
  assert!(mask.contains(Namespace::TYPE));
  assert!(mask.contains(Namespace::NAMESPACE));
  let ns_symbol = ns_group
    .symbol_for(Namespace::VALUE, symbols)
    .expect("value namespace present");
  match &symbols.symbol(ns_symbol).origin {
    SymbolOrigin::Import { from, imported } => {
      assert_eq!(from, &ModuleRef::File(file_a));
      assert_eq!(imported, "*");
    }
    other => panic!("expected import origin, got {:?}", other),
  }
}

#[test]
fn circular_export_is_cycle_safe() {
  let file_a = FileId(10);
  let file_b = FileId(11);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "foo", DeclKind::Function, Exported::Named));
  a.exports.push(Export::All(ExportAll {
    specifier: "b".to_string(),
    is_type_only: false,
    specifier_span: span(20),
    alias: None,
    alias_span: None,
  }));

  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(1, "bar", DeclKind::Var, Exported::Named));
  b.exports.push(Export::All(ExportAll {
    specifier: "a".to_string(),
    is_type_only: false,
    specifier_span: span(21),
    alias: None,
    alias_span: None,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };

  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
    "b".to_string() => file_b,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_a], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let exports_a = semantics.exports_of(file_a);
  let exports_b = semantics.exports_of(file_b);
  let symbols = semantics.symbols();

  assert!(exports_a.contains_key("foo"));
  assert!(exports_a.contains_key("bar"));
  assert!(exports_b.contains_key("foo"));
  assert!(exports_b.contains_key("bar"));

  let foo_a = exports_a
    .get("foo")
    .unwrap()
    .symbol_for(Namespace::VALUE, symbols)
    .unwrap();
  let foo_b = exports_b
    .get("foo")
    .unwrap()
    .symbol_for(Namespace::VALUE, symbols)
    .unwrap();
  assert_eq!(foo_a, foo_b);
}

#[test]
fn type_only_import_export_isolated() {
  let file_a = FileId(20);
  let file_b = FileId(21);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "Foo", DeclKind::Interface, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: span(30),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: true,
      imported_span: span(31),
      local_span: span(32),
    }],
    is_type_only: false,
  });
  b.exports.push(Export::Named(NamedExport {
    specifier: None,
    specifier_span: None,
    items: vec![ExportSpecifier {
      local: "Foo".to_string(),
      exported: None,
      local_span: span(33),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let foo_export = semantics.exports_of(file_b).get("Foo").unwrap();
  let mask = foo_export.namespaces(semantics.symbols());
  assert_eq!(mask, Namespace::TYPE);
}

#[test]
fn export_namespace_import_uses_local_binding() {
  let file_a = FileId(22);
  let file_b = FileId(23);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "Value", DeclKind::Var, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: span(40),
    default: None,
    namespace: Some(ImportNamespace {
      local: "NS".to_string(),
      local_span: span(41),
      is_type_only: false,
    }),
    named: Vec::new(),
    is_type_only: false,
  });
  b.exports.push(Export::Named(NamedExport {
    specifier: None,
    specifier_span: None,
    items: vec![ExportSpecifier {
      local: "NS".to_string(),
      exported: None,
      local_span: span(42),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(
    diags.iter().all(|d| d.code != "BIND1002"),
    "unexpected BIND1002 diagnostics: {:?}",
    diags
  );
  assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags);

  let exports = semantics.exports_of(file_b);
  let symbols = semantics.symbols();
  let ns_export = exports
    .get("NS")
    .expect("namespace import should be exported");
  let value_symbol = ns_export
    .symbol_for(Namespace::VALUE, symbols)
    .expect("value namespace exported");
  let local_symbol = semantics
    .resolve_in_module(file_b, "NS", Namespace::VALUE)
    .expect("import binding present");
  assert_eq!(value_symbol, local_symbol);
  assert_eq!(
    symbols.symbol(value_symbol).owner,
    SymbolOwner::Module(file_b)
  );
  assert!(
    ns_export.namespaces(symbols).contains(Namespace::NAMESPACE),
    "namespace import should retain namespace namespace"
  );
}

#[test]
fn declaration_merging_orders_deterministically() {
  let file = FileId(30);
  let mut hir = HirFile::module(file);

  hir
    .decls
    .push(mk_decl(0, "Merged", DeclKind::Interface, Exported::Named));
  hir
    .decls
    .push(mk_decl(1, "Merged", DeclKind::Interface, Exported::Named));
  hir
    .decls
    .push(mk_decl(2, "Space", DeclKind::Namespace, Exported::Named));
  hir
    .decls
    .push(mk_decl(3, "Space", DeclKind::Namespace, Exported::Named));
  hir
    .decls
    .push(mk_decl(4, "Combo", DeclKind::Function, Exported::Named));
  hir
    .decls
    .push(mk_decl(5, "Combo", DeclKind::Namespace, Exported::Named));
  hir
    .decls
    .push(mk_decl(6, "Enumish", DeclKind::Enum, Exported::Named));
  hir
    .decls
    .push(mk_decl(7, "Classy", DeclKind::Class, Exported::No));
  hir.exports.push(Export::Named(NamedExport {
    specifier: None,
    specifier_span: None,
    items: vec![ExportSpecifier {
      local: "Classy".to_string(),
      exported: None,
      local_span: span(50),
      exported_span: None,
    }],
    is_type_only: true,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file => Arc::new(hir),
  };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let symbols = semantics.symbols();
  let exports = semantics.exports_of(file);

  let merged_sym = exports
    .get("Merged")
    .unwrap()
    .symbol_for(Namespace::TYPE, symbols)
    .unwrap();
  let merged_decls = symbols.symbol(merged_sym).decls_for(Namespace::TYPE);
  assert_eq!(merged_decls.len(), 2);
  assert!(merged_decls
    .windows(2)
    .all(|w| symbols.decl(w[0]).order < symbols.decl(w[1]).order));

  let space_sym = exports
    .get("Space")
    .unwrap()
    .symbol_for(Namespace::NAMESPACE, symbols)
    .unwrap();
  let space_decls = symbols.symbol(space_sym).decls_for(Namespace::NAMESPACE);
  assert_eq!(space_decls.len(), 2);

  let combo = exports.get("Combo").unwrap();
  let mask = combo.namespaces(symbols);
  assert!(mask.contains(Namespace::VALUE));
  assert!(mask.contains(Namespace::NAMESPACE));
  let combo_value = combo.symbol_for(Namespace::VALUE, symbols).unwrap();
  let combo_ns = combo.symbol_for(Namespace::NAMESPACE, symbols).unwrap();
  assert_eq!(combo_value, combo_ns);

  let enumish = exports.get("Enumish").unwrap();
  let enum_value = enumish
    .symbol_for(Namespace::VALUE, symbols)
    .expect("enum value available");
  let enum_type = enumish
    .symbol_for(Namespace::TYPE, symbols)
    .expect("enum type uses same symbol");
  assert_eq!(enum_value, enum_type);

  // Type-only export of a value+type symbol should not expose value namespace.
  let classy = exports.get("Classy").unwrap();
  assert!(classy.symbol_for(Namespace::VALUE, symbols).is_none());
  assert!(classy.symbol_for(Namespace::NAMESPACE, symbols).is_none());
  assert!(classy.symbol_for(Namespace::TYPE, symbols).is_some());
  assert_eq!(classy.namespaces(symbols), Namespace::TYPE);
}

#[test]
fn unresolved_import_export_have_spans() {
  let file = FileId(50);
  let mut hir = HirFile::module(file);
  let import_span = span(1);
  let export_span = span(2);
  hir.imports.push(Import {
    specifier: "missing".to_string(),
    specifier_span: import_span,
    default: None,
    namespace: None,
    named: Vec::new(),
    is_type_only: false,
  });
  hir.exports.push(Export::All(ExportAll {
    specifier: "missing".to_string(),
    is_type_only: false,
    specifier_span: export_span,
    alias: None,
    alias_span: None,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());

  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert_eq!(diags.len(), 2);

  let messages: Vec<_> = diags.iter().map(|d| d.message.clone()).collect();
  assert_eq!(
    messages,
    vec![
      "unresolved import: missing".to_string(),
      "unresolved export: missing".to_string()
    ]
  );

  for diag in diags {
    assert_eq!(diag.code, "BIND1002");
    assert_eq!(diag.primary.file, file);
    assert!(
      diag.primary.range == import_span || diag.primary.range == export_span,
      "unexpected span: {:?}",
      diag.primary.range
    );
  }
}

#[test]
fn export_map_is_deterministic() {
  let file = FileId(40);
  let mut hir = HirFile::module(file);
  hir
    .decls
    .push(mk_decl(0, "b", DeclKind::Var, Exported::Named));
  hir
    .decls
    .push(mk_decl(1, "a", DeclKind::Var, Exported::Named));
  hir
    .decls
    .push(mk_decl(2, "c", DeclKind::Var, Exported::Named));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let names: Vec<_> = semantics.exports_of(file).keys().cloned().collect();
  assert_eq!(
    names,
    vec!["a".to_string(), "b".to_string(), "c".to_string()]
  );
}

#[test]
fn resolve_imports_point_to_origin_module() {
  let file_a = FileId(50);
  let file_b = FileId(51);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "Foo", DeclKind::Class, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: span(50),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: false,
      imported_span: span(60),
      local_span: span(61),
    }],
    is_type_only: false,
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let import_symbol = semantics
    .resolve_in_module(file_b, "Foo", Namespace::VALUE)
    .expect("import binding present");
  match &semantics.symbols().symbol(import_symbol).origin {
    SymbolOrigin::Import { from, imported } => {
      assert_eq!(from, &ModuleRef::File(file_a));
      assert_eq!(imported, "Foo");
    }
    other => panic!("expected import origin, got {:?}", other),
  }

  let origin_symbol = semantics
    .resolve_export(file_a, "Foo", Namespace::VALUE)
    .expect("origin module exports Foo");
  let origin_decls = semantics.symbol_decls(origin_symbol, Namespace::VALUE);
  assert_eq!(origin_decls.len(), 1);
  assert_eq!(semantics.symbols().decl(origin_decls[0]).file, file_a);
}

#[test]
fn import_equals_require_binds_namespace_origin() {
  let file_a = FileId(70);
  let file_b = FileId(71);

  let a = HirFile::module(file_a);

  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(0, "Foo", DeclKind::ImportBinding, Exported::No));
  b.import_equals.push(ImportEquals {
    local: "Foo".to_string(),
    local_span: span(1),
    target: ImportEqualsTarget::Require {
      specifier: "a".to_string(),
      specifier_span: span(2),
    },
    is_exported: false,
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let import_symbol = semantics
    .resolve_in_module(file_b, "Foo", Namespace::VALUE)
    .expect("import equals binding present");
  let import_data = semantics.symbols().symbol(import_symbol);
  assert!(import_data.namespaces.contains(Namespace::VALUE));
  assert!(import_data.namespaces.contains(Namespace::TYPE));
  assert!(import_data.namespaces.contains(Namespace::NAMESPACE));
  match &import_data.origin {
    SymbolOrigin::Import { from, imported } => {
      assert_eq!(from, &ModuleRef::File(file_a));
      assert_eq!(imported, "*");
    }
    other => panic!("expected import origin, got {:?}", other),
  }
}

#[test]
fn unresolved_import_reports_specifier_span() {
  let file = FileId(50);
  let mut hir = HirFile::module(file);
  let spec_range = TextRange::new(5, 15);
  hir.imports.push(Import {
    specifier: "./missing".to_string(),
    specifier_span: spec_range,
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: false,
      imported_span: span(60),
      local_span: span(61),
    }],
    is_type_only: false,
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());

  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1002");
  assert_eq!(diag.primary.file, file);
  assert_eq!(diag.primary.range, spec_range);
}

#[test]
fn declare_global_from_dts_module_merges_into_globals() {
  let file = FileId(50);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;
  let mut decl = mk_decl(0, "Foo", DeclKind::Interface, Exported::No);
  decl.is_ambient = true;
  decl.is_global = true;
  hir.decls.push(decl);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());
  assert!(semantics.global_symbols().contains_key("Foo"));
  assert!(semantics.exports_of(file).get("Foo").is_none());
}

#[test]
fn ambient_modules_lower_from_ast() {
  let source = r#"
    declare module "pkg" { export const x: number }
    import { x } from "pkg";
    export const y = x;
  "#;
  let ast = parse(source).expect("parse");
  let file = FileId(55);
  let lower = lower_file(file, HirFileKind::Dts, &ast);
  let hir = lower_to_ts_hir(&ast, &lower);

  let pkg_file = FileId(56);
  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file => Arc::new(hir),
    pkg_file => Arc::new(HirFile::module(pkg_file)),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "pkg".to_string() => pkg_file,
  });

  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let exports = semantics.exports_of(pkg_file);
  assert!(exports.contains_key("x"), "module exports should include x");
  assert!(semantics
    .resolve_export(pkg_file, "x", Namespace::VALUE)
    .is_some());
}

#[test]
fn type_only_imports_skip_value_namespace() {
  let file_a = FileId(60);
  let file_b = FileId(61);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "Foo", DeclKind::Interface, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: span(70),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: true,
      imported_span: span(71),
      local_span: span(72),
    }],
    is_type_only: false,
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  assert!(semantics
    .resolve_in_module(file_b, "Foo", Namespace::VALUE)
    .is_none());
  let type_symbol = semantics
    .resolve_in_module(file_b, "Foo", Namespace::TYPE)
    .expect("type-only import resolves in type namespace");
  match &semantics.symbols().symbol(type_symbol).origin {
    SymbolOrigin::Import {
      from: ModuleRef::File(from),
      ..
    } => assert_eq!(*from, file_a),
    other => panic!("expected import origin, got {:?}", other),
  }
}

#[test]
fn resolve_export_handles_export_star_cycles() {
  let file_a = FileId(70);
  let file_b = FileId(71);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "foo", DeclKind::Var, Exported::Named));
  a.exports.push(Export::All(ExportAll {
    specifier: "b".to_string(),
    is_type_only: false,
    specifier_span: span(80),
    alias: None,
    alias_span: None,
  }));

  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(1, "bar", DeclKind::Var, Exported::Named));
  b.exports.push(Export::All(ExportAll {
    specifier: "a".to_string(),
    is_type_only: false,
    specifier_span: span(81),
    alias: None,
    alias_span: None,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
    "b".to_string() => file_b,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_a], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let foo_a = semantics
    .resolve_export(file_a, "foo", Namespace::VALUE)
    .expect("foo exported from a");
  let foo_b = semantics
    .resolve_export(file_b, "foo", Namespace::VALUE)
    .expect("foo re-exported through b");
  assert_eq!(foo_a, foo_b);

  let bar_b = semantics
    .resolve_export(file_b, "bar", Namespace::VALUE)
    .expect("bar exported from b");
  let bar_a = semantics
    .resolve_export(file_a, "bar", Namespace::VALUE)
    .expect("bar re-exported through a");
  assert_eq!(bar_a, bar_b);
}

#[test]
fn binder_is_deterministic_across_orders_and_threads() {
  let file_a = FileId(300);
  let file_b = FileId(301);
  let file_c = FileId(302);

  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "Foo", DeclKind::Function, Exported::Named));
  a.decls
    .push(mk_decl(1, "Foo", DeclKind::Namespace, Exported::Named));
  a.decls
    .push(mk_decl(2, "TypeOnly", DeclKind::Interface, Exported::Named));

  let mut b = HirFile::module(file_b);
  b.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: span(10),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: false,
      imported_span: span(11),
      local_span: span(12),
    }],
    is_type_only: false,
  });
  b.decls
    .push(mk_decl(0, "LocalB", DeclKind::Function, Exported::Named));
  b.exports.push(Export::Named(NamedExport {
    specifier: Some("a".to_string()),
    specifier_span: Some(span(13)),
    items: vec![ExportSpecifier {
      local: "Foo".to_string(),
      exported: Some("Bar".to_string()),
      local_span: span(14),
      exported_span: Some(span(15)),
    }],
    is_type_only: false,
  }));
  b.exports.push(Export::Named(NamedExport {
    specifier: None,
    specifier_span: None,
    items: vec![ExportSpecifier {
      local: "LocalB".to_string(),
      exported: None,
      local_span: span(18),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let mut c = HirFile::module(file_c);
  c.exports.push(Export::All(ExportAll {
    specifier: "b".to_string(),
    is_type_only: false,
    specifier_span: span(17),
    alias: None,
    alias_span: None,
  }));
  c.exports.push(Export::Named(NamedExport {
    specifier: Some("a".to_string()),
    specifier_span: Some(span(19)),
    items: vec![ExportSpecifier {
      local: "TypeOnly".to_string(),
      exported: None,
      local_span: span(20),
      exported_span: None,
    }],
    is_type_only: true,
  }));
  c.decls
    .push(mk_decl(1, "Local", DeclKind::Var, Exported::Named));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
    file_c => Arc::new(c),
  };
  let resolver_map = maplit::hashmap! {
    "a".to_string() => file_a,
    "b".to_string() => file_b,
  };
  let roots = vec![file_a, file_b, file_c];

  let baseline_resolver = StaticResolver::new(resolver_map.clone());
  let (baseline, diags) = bind_ts_program(&roots, &baseline_resolver, |f| {
    files.get(&f).unwrap().clone()
  });
  assert!(diags.is_empty());
  let baseline_exports = export_snapshot(&baseline, &roots);
  let baseline_symbols = symbol_table_snapshot(baseline.symbols());

  let files = Arc::new(files);
  let resolver_map = Arc::new(resolver_map);

  let mut orders = vec![roots.clone()];
  for seed in 0..5 {
    let mut order = roots.clone();
    order.shuffle(&mut StdRng::seed_from_u64(seed + 1));
    orders.push(order);
  }

  let handles: Vec<_> = orders
    .into_iter()
    .map(|order| {
      let files = files.clone();
      let resolver_map = resolver_map.clone();
      thread::spawn(move || {
        let resolver = StaticResolver::new((*resolver_map).clone());
        let (sem, diags) = bind_ts_program(&order, &resolver, |f| files.get(&f).unwrap().clone());
        assert!(diags.is_empty());
        (
          export_snapshot(&sem, &order),
          symbol_table_snapshot(sem.symbols()),
        )
      })
    })
    .collect();

  for handle in handles {
    let (exports, symbols) = handle.join().unwrap();
    assert_eq!(exports, baseline_exports);
    assert_eq!(symbols, baseline_symbols);
  }
}

#[test]
fn unrelated_file_does_not_renumber_symbols() {
  let keep_file = FileId(310);
  let mut keep = HirFile::module(keep_file);
  keep
    .decls
    .push(mk_decl(0, "Keep", DeclKind::Var, Exported::Named));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { keep_file => Arc::new(keep) };
  let resolver = StaticResolver::new(HashMap::new());

  let (before, diags) =
    bind_ts_program(&[keep_file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());
  let keep_symbol = before
    .resolve_export(keep_file, "Keep", Namespace::VALUE)
    .expect("exported symbol");
  let keep_owner = SymbolOwner::Module(keep_file);
  let keep_symbols_before = symbols_for_owner(before.symbols(), &keep_owner);
  let keep_decls_before = decls_for_file(before.symbols(), keep_file);

  let mut with_extra = files.clone();
  let extra_file = FileId(311);
  let mut extra = HirFile::module(extra_file);
  extra
    .decls
    .push(mk_decl(1, "NewThing", DeclKind::Class, Exported::Named));
  with_extra.insert(extra_file, Arc::new(extra));

  let (after, diags_after) = bind_ts_program(&[keep_file, extra_file], &resolver, |f| {
    with_extra.get(&f).unwrap().clone()
  });
  assert!(diags_after.is_empty());
  let keep_after = after
    .resolve_export(keep_file, "Keep", Namespace::VALUE)
    .expect("keep still exported");
  let keep_symbols_after = symbols_for_owner(after.symbols(), &keep_owner);
  let keep_decls_after = decls_for_file(after.symbols(), keep_file);

  assert_eq!(keep_symbol, keep_after);
  assert_eq!(
    export_snapshot(&before, &[keep_file]),
    export_snapshot(&after, &[keep_file])
  );
  assert_eq!(keep_symbols_before, keep_symbols_after);
  assert_eq!(keep_decls_before, keep_decls_after);
}

#[test]
fn global_symbol_groups_are_deterministic() {
  let file_a = FileId(60);
  let mut a = HirFile::script(file_a);
  a.decls
    .push(mk_decl(0, "alpha", DeclKind::Var, Exported::No));
  a.decls
    .push(mk_decl(1, "zeta", DeclKind::Var, Exported::No));

  let file_b = FileId(61);
  let mut b = HirFile::script(file_b);
  b.decls
    .push(mk_decl(2, "alpha", DeclKind::Interface, Exported::No));
  b.decls
    .push(mk_decl(3, "beta", DeclKind::Interface, Exported::No));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(a),
    file_b => Arc::new(b),
  };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file_b, file_a], &resolver, |f| {
    files.get(&f).unwrap().clone()
  });
  assert!(diags.is_empty());

  let names: Vec<_> = semantics.global_symbols().keys().cloned().collect();
  assert_eq!(
    names,
    vec!["alpha".to_string(), "beta".to_string(), "zeta".to_string()]
  );

  let symbols = semantics.symbols();
  let alpha = semantics.global_symbols().get("alpha").unwrap();
  let alpha_value = alpha.symbol_for(Namespace::VALUE, symbols);
  let alpha_type = alpha.symbol_for(Namespace::TYPE, symbols);
  assert!(alpha_value.is_some());
  assert!(alpha_type.is_some());
  assert_ne!(alpha_value, alpha_type);
}

#[test]
fn duplicate_export_has_two_labels() {
  let file_a = FileId(60);
  let mut a = HirFile::module(file_a);
  a.decls
    .push(mk_decl(0, "Dup", DeclKind::Var, Exported::Named));

  let file_b = FileId(61);
  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(1, "Dup", DeclKind::Var, Exported::Named));
  b.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: TextRange::new(10, 13),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Dup".to_string(),
      local: "FromA".to_string(),
      is_type_only: false,
      imported_span: span(62),
      local_span: span(63),
    }],
    is_type_only: false,
  });
  b.exports.push(Export::Named(NamedExport {
    specifier: None,
    specifier_span: None,
    items: vec![ExportSpecifier {
      local: "FromA".to_string(),
      exported: Some("Dup".to_string()),
      local_span: span(64),
      exported_span: Some(TextRange::new(200, 203)),
    }],
    is_type_only: false,
  }));

  let files: HashMap<FileId, Arc<HirFile>> =
    maplit::hashmap! { file_a => Arc::new(a), file_b => Arc::new(b) };
  let resolver = StaticResolver::new(maplit::hashmap! { "a".to_string() => file_a });

  let (_semantics, diags) =
    bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1001");
  assert_eq!(diag.primary.file, file_b);
  assert_eq!(diag.primary.range, TextRange::new(200, 203));
  assert_eq!(diag.labels.len(), 1);
  assert_eq!(diag.labels[0].span.file, file_b);
  assert_eq!(diag.labels[0].span.range, span(1));
  assert!(!diag.labels[0].is_primary);
}

#[test]
fn duplicate_import_binding_reports_previous_span() {
  let file_main = FileId(62);
  let file_a = FileId(63);
  let file_b = FileId(64);

  let mut main = HirFile::module(file_main);
  let first_local_span = span(70);
  let second_local_span = span(80);
  main.imports.push(Import {
    specifier: "a".to_string(),
    specifier_span: TextRange::new(10, 20),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: false,
      imported_span: span(71),
      local_span: first_local_span,
    }],
    is_type_only: false,
  });
  main.imports.push(Import {
    specifier: "b".to_string(),
    specifier_span: TextRange::new(30, 40),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: false,
      imported_span: span(81),
      local_span: second_local_span,
    }],
    is_type_only: false,
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_main => Arc::new(main),
    file_a => Arc::new(HirFile::module(file_a)),
    file_b => Arc::new(HirFile::module(file_b)),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "a".to_string() => file_a,
    "b".to_string() => file_b,
  });

  let (_semantics, diags) =
    bind_ts_program(&[file_main], &resolver, |f| files.get(&f).unwrap().clone());

  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1004");
  assert_eq!(diag.message, "duplicate import binding: 'Foo'");
  assert_eq!(diag.primary.file, file_main);
  assert_eq!(diag.primary.range, second_local_span);
  assert_eq!(diag.labels.len(), 1);
  let label = &diag.labels[0];
  assert_eq!(label.span.file, file_main);
  assert_eq!(label.span.range, first_local_span);
  assert!(!label.is_primary);
}

#[test]
fn dts_script_decls_participate_in_globals() {
  let file = FileId(51);
  let mut hir = HirFile::script(file);
  hir.file_kind = FileKind::Dts;
  let mut decl = mk_decl(0, "Baz", DeclKind::Var, Exported::No);
  decl.is_ambient = true;
  hir.decls.push(decl);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());
  assert!(semantics.global_symbols().contains_key("Baz"));
}

#[test]
fn non_dts_global_augments_emit_diagnostic() {
  let file = FileId(52);
  let mut hir = HirFile::module(file);
  let mut decl = mk_decl(0, "Aug", DeclKind::Interface, Exported::No);
  decl.is_global = true;
  hir.decls.push(decl);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());

  assert!(
    diags.iter().any(|d| d.code == "BIND2001"),
    "expected unsupported augmentation diagnostic"
  );
}

#[test]
fn declare_global_interfaces_merge_in_globals() {
  let file = FileId(90);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut first = mk_decl(0, "MergedGlobal", DeclKind::Interface, Exported::No);
  first.is_ambient = true;
  first.is_global = true;
  let mut second = mk_decl(1, "MergedGlobal", DeclKind::Interface, Exported::No);
  second.is_ambient = true;
  second.is_global = true;
  hir.decls.push(first);
  hir.decls.push(second);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let symbols = semantics.symbols();
  let group = semantics
    .global_symbols()
    .get("MergedGlobal")
    .expect("global interface merged");
  let sym = group
    .symbol_for(Namespace::TYPE, symbols)
    .expect("type symbol present");
  let decls = symbols.symbol(sym).decls_for(Namespace::TYPE);
  assert_eq!(decls.len(), 2);
  assert!(decls
    .windows(2)
    .all(|w| symbols.decl(w[0]).order < symbols.decl(w[1]).order));
}

#[test]
fn global_value_namespace_merge() {
  let file = FileId(91);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut func = mk_decl(0, "ComboGlobal", DeclKind::Function, Exported::No);
  func.is_ambient = true;
  func.is_global = true;
  let mut ns = mk_decl(1, "ComboGlobal", DeclKind::Namespace, Exported::No);
  ns.is_ambient = true;
  ns.is_global = true;
  hir.decls.push(func);
  hir.decls.push(ns);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let symbols = semantics.symbols();
  let group = semantics
    .global_symbols()
    .get("ComboGlobal")
    .expect("global merge present");
  let mask = group.namespaces(symbols);
  assert!(mask.contains(Namespace::VALUE));
  assert!(mask.contains(Namespace::NAMESPACE));
  let value_sym = group.symbol_for(Namespace::VALUE, symbols).unwrap();
  let namespace_sym = group.symbol_for(Namespace::NAMESPACE, symbols).unwrap();
  assert_eq!(value_sym, namespace_sym);
}

#[test]
fn ambient_modules_collect_exports() {
  let file = FileId(92);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut decl = mk_decl(0, "AmbientValue", DeclKind::Function, Exported::No);
  decl.is_ambient = true;
  let ambient = AmbientModule {
    name: "pkg".to_string(),
    name_span: span(100),
    decls: vec![decl],
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  };
  hir.ambient_modules.push(ambient);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let exports = semantics
    .exports_of_ambient_module("pkg")
    .expect("ambient module exports available");
  let symbols = semantics.symbols();
  let symbol = exports
    .get("AmbientValue")
    .expect("ambient value exported")
    .symbol_for(Namespace::VALUE, symbols)
    .expect("value symbol available");
  let decls = symbols.symbol(symbol).decls_for(Namespace::VALUE);
  assert_eq!(decls.len(), 1);
}

#[test]
fn ambient_import_diagnostic_points_to_specifier() {
  let file = FileId(150);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let import_span = span(25);
  hir.ambient_modules.push(AmbientModule {
    name: "pkg".to_string(),
    name_span: span(10),
    decls: Vec::new(),
    imports: vec![Import {
      specifier: "missing".to_string(),
      specifier_span: import_span,
      default: None,
      namespace: None,
      named: Vec::new(),
      is_type_only: false,
    }],
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());

  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1002");
  assert_eq!(diag.primary.file, file);
  assert_eq!(diag.primary.range, import_span);
}

#[test]
fn script_exports_report_single_diagnostic_with_span() {
  let file = FileId(93);
  let mut hir = HirFile::script(file);
  hir
    .decls
    .push(mk_decl(0, "foo", DeclKind::Var, Exported::Named));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());

  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1003");
  assert_eq!(diag.primary.file, file);
  assert_eq!(diag.primary.range, span(0));
}

#[test]
fn export_assignment_reports_span() {
  let file = FileId(94);
  let mut hir = HirFile::module(file);
  hir.exports.push(Export::ExportAssignment {
    expr: "foo".to_string(),
    span: span(10),
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());

  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1002");
  assert_eq!(diag.primary.file, file);
  assert_eq!(diag.primary.range, span(10));
}

#[test]
fn export_as_namespace_reports_diagnostic() {
  let file = FileId(95);
  let mut hir = HirFile::module(file);
  hir.export_as_namespace.push(ExportAsNamespace {
    name: "Foo".to_string(),
    span: span(20),
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (_semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());

  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1003");
  assert_eq!(diag.primary.file, file);
  assert_eq!(diag.primary.range, span(20));
}

#[test]
fn dts_export_as_namespace_creates_global_symbol() {
  let file = FileId(116);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;
  hir
    .decls
    .push(mk_decl(0, "value", DeclKind::Var, Exported::Named));
  hir.export_as_namespace.push(ExportAsNamespace {
    name: "Foo".to_string(),
    span: span(30),
  });

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());

  assert!(diags.is_empty());

  let globals = semantics.global_symbols();
  assert!(globals.contains_key("Foo"));
  let symbols = semantics.symbols();
  let group = globals.get("Foo").unwrap();
  let mask = group.namespaces(symbols);
  assert!(mask.contains(Namespace::VALUE));
  assert!(mask.contains(Namespace::NAMESPACE));
  assert!(mask.contains(Namespace::TYPE));
  let sym = group.symbol_for(Namespace::VALUE, symbols).unwrap();
  match &symbols.symbol(sym).origin {
    SymbolOrigin::Import { from, imported } => {
      assert_eq!(from, &ModuleRef::File(file));
      assert_eq!(imported, "*");
    }
    other => panic!("expected import origin, got {:?}", other),
  }
}

#[test]
fn export_as_namespace_conflict_reports_diagnostic() {
  let file_a = FileId(117);
  let file_b = FileId(118);

  let mut a = HirFile::module(file_a);
  a.file_kind = FileKind::Dts;
  a.export_as_namespace.push(ExportAsNamespace {
    name: "Foo".to_string(),
    span: span(40),
  });

  let mut b = HirFile::module(file_b);
  b.file_kind = FileKind::Dts;
  b.export_as_namespace.push(ExportAsNamespace {
    name: "Foo".to_string(),
    span: span(41),
  });

  let files: HashMap<FileId, Arc<HirFile>> =
    maplit::hashmap! { file_a => Arc::new(a), file_b => Arc::new(b) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file_a, file_b], &resolver, |f| {
    files.get(&f).unwrap().clone()
  });

  assert!(semantics.global_symbols().contains_key("Foo"));
  assert_eq!(diags.len(), 1);
  let diag = &diags[0];
  assert_eq!(diag.code, "BIND1006");
  assert_eq!(diag.primary.file, file_b);
  assert_eq!(diag.primary.range, span(41));
  assert_eq!(diag.labels.len(), 1);
  assert_eq!(diag.labels[0].span.file, file_a);
  assert_eq!(diag.labels[0].span.range, span(40));
}

#[test]
fn ambient_module_fragments_merge_exports() {
  let file = FileId(96);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut part1 = AmbientModule {
    name: "pkg".to_string(),
    name_span: span(0),
    decls: Vec::new(),
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  };
  let mut func = mk_decl(0, "Aug", DeclKind::Function, Exported::No);
  func.is_ambient = true;
  part1.decls.push(func);

  let mut part2 = part1.clone();
  part2.decls.clear();
  part2
    .decls
    .push(mk_decl(1, "Aug", DeclKind::Namespace, Exported::No));

  hir.ambient_modules.push(part1);
  hir.ambient_modules.push(part2);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let exports = semantics
    .exports_of_ambient_module("pkg")
    .expect("ambient module exports present");
  let symbols = semantics.symbols();
  let group = exports.get("Aug").expect("merged symbol present");
  let mask = group.namespaces(symbols);
  assert!(mask.contains(Namespace::VALUE));
  assert!(mask.contains(Namespace::NAMESPACE));
  let value = group.symbol_for(Namespace::VALUE, symbols).unwrap();
  let ns = group.symbol_for(Namespace::NAMESPACE, symbols).unwrap();
  assert_eq!(value, ns);
}

#[test]
fn ambient_module_interfaces_merge_deterministically() {
  let file = FileId(97);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut part1 = AmbientModule {
    name: "lib".to_string(),
    name_span: span(0),
    decls: Vec::new(),
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  };
  let mut part2 = part1.clone();

  let mut iface_a = mk_decl(0, "Merged", DeclKind::Interface, Exported::No);
  iface_a.is_ambient = true;
  let mut iface_b = mk_decl(1, "Merged", DeclKind::Interface, Exported::No);
  iface_b.is_ambient = true;
  part1.decls.push(iface_a);
  part2.decls.push(iface_b);

  hir.ambient_modules.push(part1);
  hir.ambient_modules.push(part2);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let exports = semantics
    .exports_of_ambient_module("lib")
    .expect("ambient module exports present");
  let symbols = semantics.symbols();
  let merged_symbol = exports
    .get("Merged")
    .expect("interface exported")
    .symbol_for(Namespace::TYPE, symbols)
    .expect("type namespace present");
  let decls = semantics.symbol_decls(merged_symbol, Namespace::TYPE);
  assert_eq!(decls.len(), 2);
  assert!(decls
    .windows(2)
    .all(|w| symbols.decl(w[0]).order < symbols.decl(w[1]).order));
}

#[test]
fn ambient_module_import_reexports_without_resolver_mapping() {
  let file = FileId(120);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut decl = mk_decl(0, "x", DeclKind::Var, Exported::No);
  decl.is_ambient = true;
  let ambient = AmbientModule {
    name: "pkg".to_string(),
    name_span: span(0),
    decls: vec![decl],
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  };
  hir.ambient_modules.push(ambient);

  hir.imports.push(Import {
    specifier: "pkg".to_string(),
    specifier_span: span(10),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "x".to_string(),
      local: "x".to_string(),
      is_type_only: false,
      imported_span: span(11),
      local_span: span(12),
    }],
    is_type_only: false,
  });
  hir.exports.push(Export::Named(NamedExport {
    specifier: None,
    specifier_span: None,
    items: vec![ExportSpecifier {
      local: "x".to_string(),
      exported: None,
      local_span: span(13),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! { file => Arc::new(hir) };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(
    diags.is_empty(),
    "expected no diagnostics for ambient module import, got {:?}",
    diags
  );

  let symbols = semantics.symbols();
  let ambient_symbol = semantics
    .exports_of_ambient_module("pkg")
    .and_then(|exports| exports.get("x"))
    .and_then(|group| group.symbol_for(Namespace::VALUE, symbols))
    .expect("ambient export available");
  let reexported = semantics
    .exports_of(file)
    .get("x")
    .and_then(|group| group.symbol_for(Namespace::VALUE, symbols))
    .expect("module exports imported symbol");
  assert_eq!(ambient_symbol, reexported);

  let import_symbol = semantics
    .resolve_in_module(file, "x", Namespace::VALUE)
    .expect("import binding present");
  match &semantics.symbols().symbol(import_symbol).origin {
    SymbolOrigin::Import { from, imported } => {
      assert_eq!(from, &ModuleRef::Ambient("pkg".to_string()));
      assert_eq!(imported, "x");
    }
    other => panic!("expected ambient import origin, got {:?}", other),
  }
}

#[test]
fn ambient_module_reexport_chain() {
  let file_pkg = FileId(121);
  let file_reexport = FileId(122);

  let mut pkg = HirFile::module(file_pkg);
  pkg.file_kind = FileKind::Dts;
  let mut decl = mk_decl(0, "foo", DeclKind::Function, Exported::No);
  decl.is_ambient = true;
  pkg.ambient_modules.push(AmbientModule {
    name: "pkg".to_string(),
    name_span: span(0),
    decls: vec![decl],
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  });

  let mut reexport = HirFile::module(file_reexport);
  reexport.exports.push(Export::Named(NamedExport {
    specifier: Some("pkg".to_string()),
    specifier_span: Some(span(20)),
    items: vec![ExportSpecifier {
      local: "foo".to_string(),
      exported: None,
      local_span: span(21),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_pkg => Arc::new(pkg),
    file_reexport => Arc::new(reexport),
  };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file_pkg, file_reexport], &resolver, |f| {
    files.get(&f).unwrap().clone()
  });
  assert!(diags.is_empty(), "unexpected diagnostics: {:?}", diags);

  let symbols = semantics.symbols();
  let ambient_symbol = semantics
    .exports_of_ambient_module("pkg")
    .and_then(|exports| exports.get("foo"))
    .and_then(|group| group.symbol_for(Namespace::VALUE, symbols))
    .expect("ambient export present");
  let reexported_symbol = semantics
    .exports_of(file_reexport)
    .get("foo")
    .and_then(|group| group.symbol_for(Namespace::VALUE, symbols))
    .expect("re-export present");
  assert_eq!(ambient_symbol, reexported_symbol);
}

#[test]
fn external_module_augmentation_merges_without_new_exports() {
  let file_a = FileId(160);
  let mut a = HirFile::module(file_a);
  a.file_kind = FileKind::Dts;
  let mut request = mk_decl(0, "Request", DeclKind::Interface, Exported::Named);
  request.is_ambient = true;
  a.decls.push(request);

  let file_aug = FileId(161);
  let mut aug = HirFile::module(file_aug);
  aug.file_kind = FileKind::Dts;
  let mut augmented_request = mk_decl(1, "Request", DeclKind::Interface, Exported::No);
  augmented_request.is_ambient = true;
  let mut only_aug = mk_decl(2, "OnlyInAugmentation", DeclKind::Interface, Exported::No);
  only_aug.is_ambient = true;
  aug.ambient_modules.push(AmbientModule {
    name: "./a".to_string(),
    name_span: span(10),
    decls: vec![augmented_request, only_aug],
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  });

  let files: HashMap<FileId, Arc<HirFile>> =
    maplit::hashmap! { file_a => Arc::new(a), file_aug => Arc::new(aug) };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "./a".to_string() => file_a,
  });

  let (semantics, diags) =
    bind_ts_program(&[file_aug], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let request_symbol = semantics
    .resolve_export(file_a, "Request", Namespace::TYPE)
    .expect("Request exported");
  let request_decl_files: Vec<_> = semantics
    .symbol_decls(request_symbol, Namespace::TYPE)
    .iter()
    .map(|d| semantics.symbols().decl(*d).file)
    .collect();
  assert_eq!(request_decl_files.len(), 2);
  assert!(
    request_decl_files.contains(&file_a) && request_decl_files.contains(&file_aug),
    "merged declarations should include original and augmentation"
  );

  assert!(
    semantics.exports_of(file_a).get("OnlyInAugmentation").is_none(),
    "augmentation without export should not create a new export"
  );
}

#[test]
fn imports_use_ambient_modules_when_file_missing() {
  let file_import = FileId(130);
  let file_ambient = FileId(131);

  let mut importer = HirFile::module(file_import);
  importer.imports.push(Import {
    specifier: "pkg".to_string(),
    specifier_span: span(1),
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: true,
      imported_span: span(2),
      local_span: span(3),
    }],
    is_type_only: true,
  });

  let mut ambient_decl = mk_decl(0, "Foo", DeclKind::Interface, Exported::No);
  ambient_decl.is_ambient = true;
  let ambient = AmbientModule {
    name: "pkg".to_string(),
    name_span: span(4),
    decls: vec![ambient_decl],
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  };
  let mut ambient_file = HirFile::module(file_ambient);
  ambient_file.file_kind = FileKind::Dts;
  ambient_file.ambient_modules.push(ambient);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_import => Arc::new(importer),
    file_ambient => Arc::new(ambient_file),
  };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file_import, file_ambient], &resolver, |f| {
    files.get(&f).unwrap().clone()
  });
  assert!(diags.is_empty());

  let imported = semantics
    .resolve_in_module(file_import, "Foo", Namespace::TYPE)
    .expect("ambient import available");
  match &semantics.symbols().symbol(imported).origin {
    SymbolOrigin::Import {
      from: ModuleRef::Ambient(spec),
      imported,
    } => {
      assert_eq!(spec, "pkg");
      assert_eq!(imported, "Foo");
    }
    other => panic!("expected ambient import origin, got {:?}", other),
  }
}

#[test]
fn reexports_from_ambient_modules_are_resolved() {
  let file_export = FileId(132);
  let file_ambient = FileId(133);

  let mut exporter = HirFile::module(file_export);
  exporter.exports.push(Export::Named(NamedExport {
    specifier: Some("pkg".to_string()),
    specifier_span: Some(span(5)),
    items: vec![ExportSpecifier {
      local: "Foo".to_string(),
      exported: None,
      local_span: span(6),
      exported_span: None,
    }],
    is_type_only: false,
  }));

  let mut ambient_decl = mk_decl(0, "Foo", DeclKind::Interface, Exported::No);
  ambient_decl.is_ambient = true;
  let ambient = AmbientModule {
    name: "pkg".to_string(),
    name_span: span(7),
    decls: vec![ambient_decl],
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  };
  let mut ambient_file = HirFile::module(file_ambient);
  ambient_file.file_kind = FileKind::Dts;
  ambient_file.ambient_modules.push(ambient);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_export => Arc::new(exporter),
    file_ambient => Arc::new(ambient_file),
  };
  let resolver = StaticResolver::new(HashMap::new());

  let (semantics, diags) = bind_ts_program(&[file_export, file_ambient], &resolver, |f| {
    files.get(&f).unwrap().clone()
  });
  assert!(diags.is_empty());

  let ambient_exports = semantics
    .exports_of_ambient_module("pkg")
    .expect("ambient exports available");
  let ambient_symbol = ambient_exports
    .get("Foo")
    .expect("Foo exported from ambient module")
    .symbol_for(Namespace::TYPE, semantics.symbols())
    .expect("type export available");

  let exported = semantics
    .resolve_export(file_export, "Foo", Namespace::TYPE)
    .expect("re-export resolved");
  assert_eq!(exported, ambient_symbol);
}

#[test]
fn lower_ambient_module_from_dts() {
  let source = r#"declare module "pkg" { interface Foo {} }"#;
  let ast = parse(source).expect("parse");
  let lowered = lower_file(FileId(200), HirFileKind::Dts, &ast);
  let hir = lower_to_ts_hir(&ast, &lowered);

  assert_eq!(hir.module_kind, ModuleKind::Script);
  assert!(
    hir.decls.is_empty(),
    "module declaration should not be a top-level decl"
  );
  assert_eq!(hir.ambient_modules.len(), 1);

  let ambient = &hir.ambient_modules[0];
  assert_eq!(ambient.name, "pkg");
  assert!(ambient
    .decls
    .iter()
    .any(|d| d.name == "Foo" && matches!(d.kind, DeclKind::Interface)));

  let files: HashMap<FileId, Arc<HirFile>> = HashMap::from([(FileId(200), Arc::new(hir))]);
  let resolver = StaticResolver::new(HashMap::new());
  let (semantics, diags) = bind_ts_program(&[FileId(200)], &resolver, |f| {
    files.get(&f).unwrap().clone()
  });
  assert!(diags.is_empty());

  let exports = semantics
    .exports_of_ambient_module("pkg")
    .expect("ambient module exports present");
  let symbols = semantics.symbols();
  assert!(exports
    .get("Foo")
    .and_then(|group| group.symbol_for(Namespace::TYPE, symbols))
    .is_some());
}

#[test]
fn nested_module_syntax_stays_in_ambient_module() {
  let source = r#"
    declare module "pkg" {
      export interface Local {}
      export { Local as Alias };
    }
  "#;
  let ast = parse(source).expect("parse");
  let lowered = lower_file(FileId(201), HirFileKind::Dts, &ast);
  let hir = lower_to_ts_hir(&ast, &lowered);

  assert_eq!(hir.module_kind, ModuleKind::Script);
  assert!(
    hir.imports.is_empty(),
    "nested imports should not appear at file level"
  );
  assert!(
    hir.exports.is_empty(),
    "nested exports should not appear at file level"
  );
  assert!(
    hir.decls.is_empty(),
    "ambient module def should not become a decl"
  );
  assert_eq!(hir.ambient_modules.len(), 1);

  let ambient = &hir.ambient_modules[0];
  assert_eq!(ambient.exports.len(), 1);
  assert!(ambient
    .decls
    .iter()
    .any(|d| d.name == "Local" && matches!(d.kind, DeclKind::Interface)));
}

fn body_by_name<'a>(
  lowered: &'a hir_js::hir::LowerResult,
  name: &str,
  kind: DefKind,
) -> &'a hir_js::hir::Body {
  let def = lowered
    .defs
    .iter()
    .find(|d| d.path.kind == kind && lowered.names.resolve(d.path.name) == Some(name))
    .expect("definition present");
  if let Some(body_id) = def.body {
    if let Some(body) = lowered.bodies.get(body_id.0 as usize) {
      return body.as_ref();
    }
  }
  lowered
    .bodies
    .iter()
    .find(|b| b.owner == def.id)
    .or_else(|| lowered.bodies.first())
    .map(|b| b.as_ref())
    .unwrap_or_else(|| panic!("body available for {}", name))
}

#[test]
fn locals_imports_use_expected_namespaces() {
  let mut ast = parse(
    r#"
    import { foo } from "mod";
    import * as ns from "mod";
    import type { bar } from "mod";
    import baz from "mod";
  "#,
  )
  .unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(98), true);
  let root = locals.root_scope();

  let symbol_named = |name: &str| {
    locals
      .symbols
      .values()
      .find(|sym| {
        sym.decl_scope == root
          && locals
            .names
            .get(&sym.name)
            .map(|n| n == name)
            .unwrap_or(false)
      })
      .expect("symbol present")
  };

  assert_eq!(
    symbol_named("foo").namespaces,
    Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
  );
  assert_eq!(
    symbol_named("baz").namespaces,
    Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
  );
  assert_eq!(symbol_named("bar").namespaces, Namespace::TYPE);
  assert_eq!(
    symbol_named("ns").namespaces,
    Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE
  );
}

#[test]
fn module_scope_locals_map_to_program_symbols() {
  let ast_a = parse(
    r#"
    export const Foo = 1;
  "#,
  )
  .unwrap();
  let mut ast_b = parse(
    r#"
    import { Foo } from "./a";
  "#,
  )
  .unwrap();
  let file_a = FileId(99);
  let file_b = FileId(100);

  let lower_a = lower_file(file_a, HirFileKind::Ts, &ast_a);
  let lower_b = lower_file(file_b, HirFileKind::Ts, &ast_b);
  let locals_b = bind_ts_locals(&mut ast_b, file_b, true);

  let files: HashMap<FileId, Arc<HirFile>> = maplit::hashmap! {
    file_a => Arc::new(lower_to_ts_hir(&ast_a, &lower_a)),
    file_b => Arc::new(lower_to_ts_hir(&ast_b, &lower_b)),
  };
  let resolver = StaticResolver::new(maplit::hashmap! {
    "./a".to_string() => file_a,
  });

  let (program, diags) = bind_ts_program(&[file_b], &resolver, |f| files.get(&f).unwrap().clone());
  assert!(diags.is_empty());

  let mapping = map_module_scope_locals_to_program(&locals_b, &program, file_b);
  let local_foo = locals_b
    .symbols
    .values()
    .find(|sym| {
      sym.decl_scope == locals_b.root_scope()
        && locals_b
          .names
          .get(&sym.name)
          .map(|n| n == "Foo")
          .unwrap_or(false)
    })
    .expect("local Foo binding present")
    .id;
  let program_foo = program
    .resolve_in_module(file_b, "Foo", Namespace::VALUE)
    .expect("program import symbol present");
  assert_eq!(mapping.get(&local_foo), Some(&program_foo));
}

#[test]
fn locals_resolve_block_shadowing() {
  let mut ast = parse(
    r#"
    function f() {
      var x = 1;
      {
        let x = 2;
        x;
      }
      x;
    }
  "#,
  )
  .unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(90), true);
  let lowered = lower_file(FileId(90), HirFileKind::Ts, &ast);
  let body = body_by_name(&lowered, "f", DefKind::Function);

  let mut id_uses: Vec<_> = body
    .exprs
    .iter()
    .enumerate()
    .filter_map(|(idx, expr)| match expr.kind {
      ExprKind::Ident(_) => Some((ExprId(idx as u32), expr.span)),
      _ => None,
    })
    .collect();
  id_uses.sort_by_key(|(_, span)| span.start);
  assert_eq!(id_uses.len(), 2);

  let inner = locals
    .resolve_expr(body, id_uses[0].0)
    .expect("inner use resolves");
  let outer = locals
    .resolve_expr(body, id_uses[1].0)
    .expect("outer use resolves");
  assert_ne!(inner, outer);
}

#[test]
fn locals_hoist_var_declarations() {
  let mut ast = parse(
    r#"
    function g() {
      x;
      var x = 1;
    }
  "#,
  )
  .unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(91), true);
  let lowered = lower_file(FileId(91), HirFileKind::Ts, &ast);
  let body = body_by_name(&lowered, "g", DefKind::Function);

  let first_ident = body
    .exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      ExprKind::Ident(_) => Some(ExprId(idx as u32)),
      _ => None,
    })
    .expect("identifier present");
  assert!(locals.resolve_expr(body, first_ident).is_some());
}

#[test]
fn locals_separate_value_and_type_namespaces() {
  let mut ast = parse(
    r#"
    type Foo = number;
    const Foo = 1;
    type Bar = Foo;
    const baz = Foo;
  "#,
  )
  .unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(92), true);
  let lowered = lower_file(FileId(92), HirFileKind::Ts, &ast);

  let mut type_ref = None;
  let mut type_arenas = None;
  for arenas in lowered.types.values() {
    if let Some((idx, _)) = arenas
      .type_exprs
      .iter()
      .enumerate()
      .find(|(_, expr)| matches!(expr.kind, TypeExprKind::TypeRef(_)))
    {
      type_ref = Some(TypeExprId(idx as u32));
      type_arenas = Some(arenas);
      break;
    }
  }
  let type_arenas = type_arenas.expect("type arenas present");
  let type_ref = type_ref.expect("type reference present");
  let type_sym = locals
    .resolve_type_name(&type_arenas.type_exprs, type_ref)
    .expect("type Foo resolves");

  let baz_body = body_by_name(&lowered, "baz", DefKind::Var);
  let value_ident = baz_body
    .exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      ExprKind::Ident(_) => Some(ExprId(idx as u32)),
      _ => None,
    })
    .expect("value use present");
  let value_sym = locals
    .resolve_expr(baz_body, value_ident)
    .expect("value Foo resolves");

  assert_ne!(type_sym, value_sym);
}

#[test]
fn type_only_imports_skip_value_resolution() {
  let mut ast = parse(
    r#"
    import type { Foo } from "mod";
    type Bar = Foo;
    const value = Foo;
  "#,
  )
  .unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(93), true);
  let lowered = lower_file(FileId(93), HirFileKind::Ts, &ast);

  let mut type_ref = None;
  let mut type_arenas = None;
  for arenas in lowered.types.values() {
    if let Some((idx, _)) = arenas
      .type_exprs
      .iter()
      .enumerate()
      .find(|(_, expr)| matches!(expr.kind, TypeExprKind::TypeRef(_)))
    {
      type_ref = Some(TypeExprId(idx as u32));
      type_arenas = Some(arenas);
      break;
    }
  }
  let type_arenas = type_arenas.expect("type arenas present");
  let type_ref = type_ref.expect("type ref present");
  assert!(
    locals
      .resolve_type_name(&type_arenas.type_exprs, type_ref)
      .is_some(),
    "type import remains available"
  );

  let value_body = body_by_name(&lowered, "value", DefKind::Var);
  let id = value_body
    .exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      ExprKind::Ident(_) => Some(ExprId(idx as u32)),
      _ => None,
    })
    .expect("value identifier present");
  assert!(
    locals.resolve_expr(value_body, id).is_none(),
    "type-only import should not resolve in value namespace"
  );
}

#[test]
fn typeof_queries_use_value_namespace() {
  let source = "type Foo = number;\nconst Foo = 1;\ntype Q = typeof Foo;\n";
  let mut ast = parse(source).unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(94), true);

  let type_alias_offset = source.find("type Foo").unwrap() + "type ".len();
  let type_sym = locals
    .resolve_expr_at_offset(type_alias_offset as u32)
    .expect("type alias binding present")
    .1;

  let value_offset = source.find("const Foo").unwrap() + "const ".len();
  let value_sym = locals
    .resolve_expr_at_offset(value_offset as u32)
    .expect("value binding present")
    .1;

  assert_ne!(type_sym, value_sym, "type and value symbols should differ");

  let query_offset = source.rfind("Foo").unwrap() as u32;
  let (_, query_sym) = locals
    .resolve_type_at_offset(query_offset)
    .expect("typeof Foo should resolve");
  assert_eq!(
    query_sym, value_sym,
    "typeof queries should use the value namespace"
  );
}

#[test]
fn qualified_type_references_use_namespace_space() {
  let source = "namespace NS { export type Foo = number; }\ntype Bar = NS.Foo;\n";
  let mut ast = parse(source).unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(95), true);

  let ns_decl = ast
    .stx
    .body
    .iter()
    .find_map(|stmt| match &*stmt.stx {
      parse_js::ast::stmt::Stmt::NamespaceDecl(ns) => Some(ns),
      _ => None,
    })
    .expect("namespace declaration present");
  let ns_symbol = ts::declared_symbol(&ns_decl.assoc).expect("namespace symbol recorded");

  let ns_qual_offset = source.find("NS.Foo").unwrap() as u32;
  let (_, resolved) = locals
    .resolve_type_at_offset(ns_qual_offset)
    .expect("qualified type should resolve");

  assert_eq!(
    resolved, ns_symbol,
    "qualified type references should resolve to the namespace symbol"
  );
  assert!(
    locals
      .symbol(resolved)
      .namespaces
      .contains(Namespace::NAMESPACE),
    "resolved symbol should live in the namespace namespace"
  );
}

#[test]
fn import_type_qualifier_ignores_local_symbols() {
  let src = r#"
    type Foo = number;
    type Bar = import("pkg").Foo;
  "#;
  let mut ast = parse(src).unwrap();
  let locals = bind_ts_locals(&mut ast, FileId(130), true);

  let local_foo = locals
    .resolve_expr_at_offset(src.find("Foo = number").expect("local Foo present") as u32)
    .expect("local Foo resolves")
    .1;

  let import_foo_offset = src.rfind("Foo").expect("import qualifier present") as u32;

  assert!(
    locals
      .resolve_type_at_offset(import_foo_offset)
      .map(|(_, sym)| sym != local_foo)
      .unwrap_or(true),
    "import type qualifier should not resolve to local Foo"
  );
}

#[test]
fn block_function_is_lexical_in_modules() {
  let source = "function outer() { if (true) { function foo() {} foo; } foo; }";
  let mut ast = parse_js::parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse module source");

  let locals = bind_ts_locals(&mut ast, FileId(200), true);
  let positions = positions(source, "foo");
  assert_eq!(positions.len(), 3, "expected three foo occurrences");
  let decl_symbol = locals
    .resolve_expr_at_offset(positions[0])
    .map(|(_, sym)| sym)
    .expect("function declaration resolves");
  let inner_use_symbol = locals
    .resolve_expr_at_offset(positions[1])
    .map(|(_, sym)| sym)
    .expect("inner block use resolves");
  let outer_symbol = locals.resolve_expr_at_offset(positions[2]);

  assert_eq!(
    decl_symbol, inner_use_symbol,
    "block use should see block-scoped function binding in modules"
  );
  assert!(
    outer_symbol.is_none(),
    "block-scoped function should not resolve outside its block in modules"
  );
}

#[test]
fn block_function_hoists_in_scripts() {
  let source = "function outer() { if (true) { function foo() {} foo; } foo; }";
  let mut ast = parse_js::parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Script,
    },
  )
  .expect("parse script source");

  let locals = bind_ts_locals(&mut ast, FileId(201), false);
  let positions = positions(source, "foo");
  assert_eq!(positions.len(), 3, "expected three foo occurrences");
  let decl_symbol = locals
    .resolve_expr_at_offset(positions[0])
    .map(|(_, sym)| sym)
    .expect("function declaration resolves");
  let inner_use_symbol = locals
    .resolve_expr_at_offset(positions[1])
    .map(|(_, sym)| sym)
    .expect("inner block use resolves");
  let outer_use_symbol = locals
    .resolve_expr_at_offset(positions[2])
    .map(|(_, sym)| sym)
    .expect("outer use should resolve in scripts");

  assert_eq!(decl_symbol, inner_use_symbol, "inner use matches decl");
  assert_eq!(
    decl_symbol, outer_use_symbol,
    "non-module scripts hoist block function declarations"
  );
}
