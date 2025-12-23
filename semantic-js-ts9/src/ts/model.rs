use bitflags::bitflags;
use std::collections::BTreeMap;

bitflags! {
  /// TypeScript has three namespaces: value, type, and namespace.
  /// Namespaces can be combined for merged symbols.
  #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
  pub struct Namespace: u8 {
    const VALUE = 0b001;
    const TYPE = 0b010;
    const NAMESPACE = 0b100;
  }
}

impl Namespace {
  pub fn is_single(self) -> bool {
    self == Namespace::VALUE || self == Namespace::TYPE || self == Namespace::NAMESPACE
  }

  pub fn iter_bits(self) -> impl Iterator<Item = Namespace> {
    [Namespace::VALUE, Namespace::TYPE, Namespace::NAMESPACE]
      .into_iter()
      .filter(move |bit| self.contains(*bit))
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
  Function,
  Class,
  Var,
  Interface,
  TypeAlias,
  Enum,
  Namespace,
  ImportBinding,
}

impl DeclKind {
  pub fn namespaces(&self) -> Namespace {
    match self {
      DeclKind::Function | DeclKind::Var => Namespace::VALUE,
      DeclKind::Class => Namespace::VALUE | Namespace::TYPE,
      DeclKind::Interface => Namespace::TYPE,
      DeclKind::TypeAlias => Namespace::TYPE,
      DeclKind::Enum => Namespace::VALUE | Namespace::TYPE,
      DeclKind::Namespace => Namespace::VALUE | Namespace::NAMESPACE,
      DeclKind::ImportBinding => Namespace::VALUE | Namespace::TYPE | Namespace::NAMESPACE,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleKind {
  Module,
  Script,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exported {
  No,
  Named,
  Default,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
  pub def_id: DefId,
  pub name: String,
  pub kind: DeclKind,
  pub is_ambient: bool,
  pub exported: Exported,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
  pub specifier: String,
  pub default: Option<ImportDefault>,
  pub namespace: Option<ImportNamespace>,
  pub named: Vec<ImportNamed>,
  /// `import type` marks the entire import as type-only.
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDefault {
  pub local: String,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportNamespace {
  pub local: String,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportNamed {
  pub imported: String,
  pub local: String,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportSpecifier {
  pub local: String,
  pub exported: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedExport {
  pub specifier: Option<String>,
  pub items: Vec<ExportSpecifier>,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportAll {
  pub specifier: String,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Export {
  Named(NamedExport),
  All(ExportAll),
  /// `export =` assignments are tracked for diagnostics.
  ExportAssignment(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirFile {
  pub file_id: FileId,
  pub module_kind: ModuleKind,
  pub decls: Vec<Decl>,
  pub imports: Vec<Import>,
  pub exports: Vec<Export>,
}

impl HirFile {
  pub fn module(file_id: FileId) -> Self {
    HirFile {
      file_id,
      module_kind: ModuleKind::Module,
      decls: Vec::new(),
      imports: Vec::new(),
      exports: Vec::new(),
    }
  }
}

#[derive(Clone, Debug)]
pub struct DeclData {
  pub id: DeclId,
  pub def_id: DefId,
  pub file: FileId,
  pub name: String,
  pub kind: DeclKind,
  pub namespaces: Namespace,
  pub is_ambient: bool,
  pub order: u32,
}

#[derive(Clone, Debug)]
pub enum SymbolOrigin {
  Local,
  Import {
    from: Option<FileId>,
    imported: String,
  },
}

#[derive(Clone, Debug)]
pub struct SymbolData {
  pub id: SymbolId,
  pub name: String,
  pub namespaces: Namespace,
  pub decls: [Vec<DeclId>; 3],
  pub origin: SymbolOrigin,
}

impl SymbolData {
  pub fn decls_for(&self, ns: Namespace) -> &Vec<DeclId> {
    &self.decls[ns_index(ns)]
  }

  pub fn decls_for_mut(&mut self, ns: Namespace) -> &mut Vec<DeclId> {
    &mut self.decls[ns_index(ns)]
  }
}

#[derive(Clone, Debug)]
pub enum SymbolGroupKind {
  Separate {
    value: Option<SymbolId>,
    ty: Option<SymbolId>,
    namespace: Option<SymbolId>,
  },
  Merged(SymbolId),
}

#[derive(Clone, Debug)]
pub struct SymbolGroup {
  pub kind: SymbolGroupKind,
}

impl SymbolGroup {
  pub fn empty() -> Self {
    SymbolGroup {
      kind: SymbolGroupKind::Separate {
        value: None,
        ty: None,
        namespace: None,
      },
    }
  }

  pub fn merged(symbol: SymbolId) -> Self {
    SymbolGroup {
      kind: SymbolGroupKind::Merged(symbol),
    }
  }

  pub fn namespaces(&self, symbols: &SymbolTable) -> Namespace {
    match &self.kind {
      SymbolGroupKind::Merged(sym) => symbols.symbol(*sym).namespaces,
      SymbolGroupKind::Separate {
        value,
        ty,
        namespace,
      } => {
        let mut ns = Namespace::empty();
        if value.is_some() {
          ns |= Namespace::VALUE;
        }
        if ty.is_some() {
          ns |= Namespace::TYPE;
        }
        if namespace.is_some() {
          ns |= Namespace::NAMESPACE;
        }
        ns
      }
    }
  }

  pub fn symbol_for(&self, ns: Namespace, symbols: &SymbolTable) -> Option<SymbolId> {
    match &self.kind {
      SymbolGroupKind::Merged(sym) => {
        if symbols.symbol(*sym).namespaces.contains(ns) {
          Some(*sym)
        } else {
          None
        }
      }
      SymbolGroupKind::Separate {
        value,
        ty,
        namespace,
      } => match ns {
        Namespace::VALUE => value.and_then(|s| {
          if symbols.symbol(s).namespaces.contains(Namespace::VALUE) {
            Some(s)
          } else {
            None
          }
        }),
        Namespace::TYPE => ty.and_then(|s| {
          if symbols.symbol(s).namespaces.contains(Namespace::TYPE) {
            Some(s)
          } else {
            None
          }
        }),
        Namespace::NAMESPACE => namespace.and_then(|s| {
          if symbols.symbol(s).namespaces.contains(Namespace::NAMESPACE) {
            Some(s)
          } else {
            None
          }
        }),
        _ => None,
      },
    }
  }
}

pub type ExportMap = BTreeMap<String, SymbolGroup>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
  pub code: &'static str,
  pub message: String,
  pub file: Option<FileId>,
}

pub trait Resolver {
  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId>;
}

#[derive(Default, Clone, Debug)]
pub struct SymbolTable {
  pub(crate) symbols: Vec<SymbolData>,
  pub(crate) decls: Vec<DeclData>,
  next_def: u32,
}

impl SymbolTable {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    &self.symbols[id.0 as usize]
  }

  pub fn symbol_mut(&mut self, id: SymbolId) -> &mut SymbolData {
    &mut self.symbols[id.0 as usize]
  }

  pub fn decl(&self, id: DeclId) -> &DeclData {
    &self.decls[id.0 as usize]
  }

  pub fn alloc_decl(
    &mut self,
    file: FileId,
    name: String,
    kind: DeclKind,
    namespaces: Namespace,
    is_ambient: bool,
    order: u32,
    def_id: Option<DefId>,
  ) -> DeclId {
    let def = def_id.unwrap_or_else(|| {
      let id = DefId(self.next_def);
      self.next_def += 1;
      id
    });
    if def.0 >= self.next_def {
      self.next_def = def.0 + 1;
    }
    let id = DeclId(self.decls.len() as u32);
    self.decls.push(DeclData {
      id,
      def_id: def,
      file,
      name,
      kind,
      namespaces,
      is_ambient,
      order,
    });
    id
  }

  pub fn alloc_symbol(
    &mut self,
    name: &str,
    namespaces: Namespace,
    origin: SymbolOrigin,
  ) -> SymbolId {
    let id = SymbolId(self.symbols.len() as u32);
    self.symbols.push(SymbolData {
      id,
      name: name.to_string(),
      namespaces,
      decls: Default::default(),
      origin,
    });
    id
  }

  pub fn add_decl_to_symbol(&mut self, symbol: SymbolId, decl: DeclId, namespaces: Namespace) {
    {
      let sym = self.symbol_mut(symbol);
      sym.namespaces |= namespaces;
    }

    for bit in namespaces.iter_bits() {
      let mut list = {
        let sym = self.symbol_mut(symbol);
        let list_ref = sym.decls_for_mut(bit);
        list_ref.push(decl);
        std::mem::take(list_ref)
      };
      list.sort_by_key(|d| self.decl(*d).order);
      list.dedup();
      self.symbol_mut(symbol).decls[ns_index(bit)] = list;
    }
  }
}

pub(crate) fn ns_index(ns: Namespace) -> usize {
  match ns {
    Namespace::VALUE => 0,
    Namespace::TYPE => 1,
    Namespace::NAMESPACE => 2,
    _ => panic!("expected single namespace bit"),
  }
}

#[derive(Clone, Debug)]
pub struct TsProgramSemantics {
  pub(crate) symbols: SymbolTable,
  pub(crate) module_exports: BTreeMap<FileId, ExportMap>,
  pub(crate) global_symbols: BTreeMap<String, SymbolGroup>,
}

impl TsProgramSemantics {
  pub fn exports_of(&self, file: FileId) -> &ExportMap {
    self
      .module_exports
      .get(&file)
      .expect("exports available for file")
  }

  pub fn symbols(&self) -> &SymbolTable {
    &self.symbols
  }

  pub fn global_symbols(&self) -> &BTreeMap<String, SymbolGroup> {
    &self.global_symbols
  }
}

#[derive(Clone, Debug)]
pub(crate) struct ImportEntry {
  pub local: String,
  pub from: Option<FileId>,
  pub imported: ImportItem,
  pub type_only: bool,
}

#[derive(Clone, Debug)]
pub(crate) enum ImportItem {
  Named(String),
  Default,
  Namespace,
}

pub(crate) type SymbolGroups = BTreeMap<String, SymbolGroup>;
