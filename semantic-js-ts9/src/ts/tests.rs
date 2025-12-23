use super::*;
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
    exported,
  }
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
    items: vec![ExportSpecifier {
      local: "foo".to_string(),
      exported: None,
    }],
    is_type_only: false,
  }));

  let mut c = HirFile::module(file_c);
  c.exports.push(Export::All(ExportAll {
    specifier: "b".to_string(),
    is_type_only: false,
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
  }));

  let mut b = HirFile::module(file_b);
  b.decls
    .push(mk_decl(1, "bar", DeclKind::Var, Exported::Named));
  b.exports.push(Export::All(ExportAll {
    specifier: "a".to_string(),
    is_type_only: false,
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
    default: None,
    namespace: None,
    named: vec![ImportNamed {
      imported: "Foo".to_string(),
      local: "Foo".to_string(),
      is_type_only: true,
    }],
    is_type_only: false,
  });
  b.exports.push(Export::Named(NamedExport {
    specifier: None,
    items: vec![ExportSpecifier {
      local: "Foo".to_string(),
      exported: None,
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
    items: vec![ExportSpecifier {
      local: "Classy".to_string(),
      exported: None,
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
  assert_eq!(names, vec![
    "a".to_string(),
    "b".to_string(),
    "c".to_string()
  ]);
}
