use super::*;
use crate::assoc::{js, ts};
use crate::ts::locals::{bind_ts_locals, SymbolId as LocalSymbolId};
use hir_js::hir::{ExprKind, FileKind as HirFileKind, TypeExprKind};
use hir_js::ids::{DefKind, ExprId, TypeExprId};
use hir_js::lower_file;
use parse_js::ast::node::NodeAssocData;
use parse_js::parse;
use std::any::TypeId;
use std::collections::HashMap;
use std::sync::Arc;

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

#[test]
fn ts_assoc_helpers_round_trip() {
  let mut assoc = NodeAssocData::default();
  let declared = ts::DeclaredSymbol(LocalSymbolId(123));
  let resolved = LocalSymbolId(456);

  assoc.set(declared);
  assoc.set(ts::ResolvedSymbol(Some(resolved)));

  assert_eq!(ts::declared_symbol(&assoc), Some(declared.0));
  assert_eq!(ts::resolved_symbol(&assoc), Some(resolved));
}

#[test]
fn ts_assoc_keys_do_not_overlap_js_accessors() {
  let mut assoc = NodeAssocData::default();
  assoc.set(ts::DeclaredSymbol(LocalSymbolId(7)));
  assoc.set(ts::ResolvedSymbol(Some(LocalSymbolId(9))));

  assert_eq!(js::declared_symbol(&assoc), None);
  assert_eq!(js::resolved_symbol(&assoc), None);
  assert_eq!(ts::declared_symbol(&assoc), Some(LocalSymbolId(7)));
  assert_eq!(ts::resolved_symbol(&assoc), Some(LocalSymbolId(9)));

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
  let _: Option<LocalSymbolId> = ts::declared_symbol(&assoc);
  let _: Option<LocalSymbolId> = ts::resolved_symbol(&assoc);
  let _: Option<crate::js::SymbolId> = js::declared_symbol(&assoc);
  let _: Option<crate::js::SymbolId> = js::resolved_symbol(&assoc);
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
  }));

  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(1, "bar", DeclKind::Var, Exported::Named));
  b.exports.push(Export::All(ExportAll {
    specifier: "a".to_string(),
    is_type_only: false,
    specifier_span: span(21),
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
  match semantics.symbols().symbol(import_symbol).origin {
    SymbolOrigin::Import { from, ref imported } => {
      assert_eq!(from, Some(file_a));
      assert_eq!(imported, "Foo");
    }
    ref other => panic!("expected import origin, got {:?}", other),
  }

  let origin_symbol = semantics
    .resolve_export(file_a, "Foo", Namespace::VALUE)
    .expect("origin module exports Foo");
  let origin_decls = semantics.symbol_decls(origin_symbol, Namespace::VALUE);
  assert_eq!(origin_decls.len(), 1);
  assert_eq!(semantics.symbols().decl(origin_decls[0]).file, file_a);
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
  match semantics.symbols().symbol(type_symbol).origin {
    SymbolOrigin::Import { from, .. } => assert_eq!(from, Some(file_a)),
    ref other => panic!("expected import origin, got {:?}", other),
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
  }));

  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(1, "bar", DeclKind::Var, Exported::Named));
  b.exports.push(Export::All(ExportAll {
    specifier: "a".to_string(),
    is_type_only: false,
    specifier_span: span(81),
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
  assert_eq!(diag.code, "BIND1003");
  assert_eq!(diag.primary.file, file);
  assert_eq!(diag.primary.range, span(10));
}

#[test]
fn export_as_namespace_reports_diagnostic() {
  let file = FileId(95);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;
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
fn ambient_module_fragments_merge_exports() {
  let file = FileId(96);
  let mut hir = HirFile::module(file);
  hir.file_kind = FileKind::Dts;

  let mut part1 = AmbientModule {
    name: "pkg".to_string(),
    name_span: span(0),
    decls: Vec::new(),
    imports: Vec::new(),
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

fn body_by_name<'a>(
  lowered: &'a hir_js::hir::LowerResult,
  name: &str,
  kind: DefKind,
) -> &'a hir_js::hir::Body {
  let def = lowered
    .defs
    .iter()
    .find(|d| d.path.kind == kind && lowered.names.resolve(d.path.name).as_deref() == Some(name))
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
  let locals = bind_ts_locals(&mut ast, true);
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
  let locals = bind_ts_locals(&mut ast, true);
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
  let locals = bind_ts_locals(&mut ast, true);
  let lowered = lower_file(FileId(92), HirFileKind::Ts, &ast);

  let type_ref = lowered
    .types
    .type_exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      TypeExprKind::TypeRef(_) => Some(TypeExprId(idx as u32)),
      _ => None,
    })
    .expect("type reference present");
  let type_sym = locals
    .resolve_type_name(&lowered.types.type_exprs, type_ref)
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
  let locals = bind_ts_locals(&mut ast, true);
  let lowered = lower_file(FileId(93), HirFileKind::Ts, &ast);

  let type_ref = lowered
    .types
    .type_exprs
    .iter()
    .enumerate()
    .find_map(|(idx, expr)| match expr.kind {
      TypeExprKind::TypeRef(_) => Some(TypeExprId(idx as u32)),
      _ => None,
    })
    .expect("type ref present");
  assert!(
    locals
      .resolve_type_name(&lowered.types.type_exprs, type_ref)
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
