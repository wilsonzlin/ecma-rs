//! Binder data model for TypeScript mode.
//!
//! The TS binder operates in the three TypeScript namespaces (`value`, `type`,
//! and `namespace`) and groups declarations by name into [`SymbolGroup`]s. Each
//! [`SymbolData`] holds the merged declarations for the namespaces it
//! participates in. IDs are content-addressed so merged overloads and exports
//! remain stable regardless of traversal order.
//!
//! File identity and diagnostics reuse shared workspace types from
//! [`diagnostics`], and declaration IDs are shared with HIR via
//! [`hir_js::DefId`] so consumers can correlate symbols with lowered
//! definitions.
//!
//! A [`HirFile`] describes a single module or script's top-level declarations,
//! imports, and exports. [`bind_ts_program`](crate::ts::bind_ts_program) walks
//! these files with a host-provided [`Resolver`] to build:
//! - a [`SymbolTable`] of all merged symbols across the program (with stable
//!   `SymbolId`/`DeclId` indices),
//! - per-file [`ExportMap`]s keyed by name in sorted order,
//! - a map of merged global symbol groups for consumers that want a holistic
//!   view.
//! - ambient module export/symbol maps addressable by module specifier strings.
//!
//! The binder currently focuses on module graph semantics and declaration
//! merging. It does not model statement-level scopes, contextual type-only
//! exports beyond the supplied `is_type_only` flags, or general `export =`
//! expressions beyond entity-name style references (identifier/property access
//! chains). Unsupported `export =` expressions are reported deterministically
//! via diagnostics. Export assignments synthesize an `export=` entry (matching
//! TypeScript's internal export name) and are represented as synthetic alias
//! declarations so downstream consumers can distinguish them from
//! `export default`.
//!
//! Binder diagnostics use the shared [`diagnostics`] crate with stable codes:
//! - `BIND1001`: duplicate export
//! - `BIND1002`: unresolved import/export or missing export
//! - `BIND1003`: unsupported export assignment expression or exports in a script
//!   module
//! - `BIND1004`: duplicate import binding
//! - `TS2309`: `export =` combined with other exports
//! - `BIND1006`: conflicting `export as namespace` declarations across modules
//!
//! ## Determinism expectations
//!
//! - Export maps and global symbol maps use [`BTreeMap`] to provide stable,
//!   sorted iteration for public APIs.
//! - Declaration lists inside symbols are sorted by their `order` field, which
//!   increments deterministically as HIR declarations are visited.
//! - `SymbolId`, `DeclId`, and synthetic `DefId` allocation is derived from
//!   stable content (file id, names, namespaces, declaration kinds, and spans) so
//!   different root orders or threads produce identical outputs.
//! - Binder diagnostics are sorted before being returned to avoid any accidental
//!   dependency on hash map iteration order.
//! - Internal caches may use hash maps, but public APIs avoid exposing their
//!   iteration order.
//!
//! ## Namespaces and merging
//!
//! - Every declaration carries a [`Namespace`] mask derived from its [`DeclKind`]
//!   (e.g. classes occupy value+type, enums value+type, namespaces value+namespace).
//! - [`SymbolGroup`]s hold up to one symbol per namespace (`Separate`) or a
//!   single merged symbol (`Merged`) when declaration kinds allow combining
//!   value/namespace (functions/classes/enums with namespaces). Interface and
//!   namespace merging are represented by multiple declarations attached to the
//!   same symbol, ordered by `DeclData::order`.
//! - Imports are modeled as [`DeclKind::ImportBinding`] that participate in all
//!   three namespaces unless marked type-only.
//! - Exports store [`SymbolGroup`]s per name; type-only exports filter out the
//!   value/namespace bits before insertion.
use crate::hash::{stable_hash, stable_hash_u32};
use bitflags::bitflags;
pub use diagnostics::{Diagnostic, FileId, Span, TextRange};
pub use hir_js::DefId;
use std::collections::BTreeMap;

bitflags! {
  /// TypeScript has three namespaces: value, type, and namespace.
  /// Namespaces can be combined for merged symbols.
  #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
pub struct SymbolId(pub u64);

impl SymbolId {
  pub fn raw(self) -> u64 {
    self.0
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

fn stable_symbol_id(owner: &SymbolOwner, name: &str, namespaces: Namespace) -> SymbolId {
  SymbolId(stable_hash(&(owner, name, namespaces.bits())))
}

fn stable_decl_id(
  file: FileId,
  name: &str,
  kind: &DeclKind,
  namespaces: Namespace,
  def_id: DefId,
  order: u32,
) -> DeclId {
  let hash = stable_hash(&(file, name, kind, namespaces.bits(), def_id.0, order));
  DeclId(hash)
}

fn synthetic_def_id(file: FileId, name: &str, kind: &DeclKind, order: u32) -> DefId {
  DefId(stable_hash_u32(&(file, name, kind, order)))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleKind {
  Module,
  Script,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileKind {
  Ts,
  Dts,
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
  pub is_global: bool,
  pub exported: Exported,
  pub span: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
  pub specifier: String,
  pub specifier_span: TextRange,
  pub default: Option<ImportDefault>,
  pub namespace: Option<ImportNamespace>,
  pub named: Vec<ImportNamed>,
  /// `import type` marks the entire import as type-only.
  pub is_type_only: bool,
}

/// `import("specifier")` type references.
///
/// These do not create bindings, but they do introduce module graph edges that
/// must be traversed so dependent modules are bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeImport {
  pub specifier: String,
  pub specifier_span: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDefault {
  pub local: String,
  pub local_span: TextRange,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportNamespace {
  pub local: String,
  pub local_span: TextRange,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportNamed {
  pub imported: String,
  pub local: String,
  pub is_type_only: bool,
  pub imported_span: TextRange,
  pub local_span: TextRange,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportEquals {
  pub local: String,
  pub local_span: TextRange,
  pub target: ImportEqualsTarget,
  pub is_exported: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportEqualsTarget {
  Require {
    specifier: String,
    specifier_span: TextRange,
  },
  EntityName {
    path: Vec<String>,
    span: TextRange,
  },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportSpecifier {
  pub local: String,
  pub exported: Option<String>,
  pub local_span: TextRange,
  pub exported_span: Option<TextRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedExport {
  pub specifier: Option<String>,
  pub specifier_span: Option<TextRange>,
  pub items: Vec<ExportSpecifier>,
  pub is_type_only: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportAll {
  pub specifier: String,
  pub is_type_only: bool,
  pub specifier_span: TextRange,
  pub alias: Option<String>,
  pub alias_span: Option<TextRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Export {
  Named(NamedExport),
  All(ExportAll),
  /// `export =` assignments are tracked for diagnostics.
  ExportAssignment {
    /// Entity name path of the RHS expression, if it is an identifier or dotted
    /// property access chain.
    path: Option<Vec<String>>,
    /// Span covering the RHS expression.
    expr_span: TextRange,
    /// Span covering the full `export =` statement.
    span: TextRange,
  },
}

/// `export as namespace Foo;`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportAsNamespace {
  pub name: String,
  pub span: TextRange,
}

/// `declare module "specifier" { ... }`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmbientModule {
  pub name: String,
  pub name_span: TextRange,
  pub decls: Vec<Decl>,
  pub imports: Vec<Import>,
  pub type_imports: Vec<TypeImport>,
  pub import_equals: Vec<ImportEquals>,
  pub exports: Vec<Export>,
  pub export_as_namespace: Vec<ExportAsNamespace>,
  pub ambient_modules: Vec<AmbientModule>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirFile {
  pub file_id: FileId,
  pub module_kind: ModuleKind,
  pub file_kind: FileKind,
  pub decls: Vec<Decl>,
  pub imports: Vec<Import>,
  pub type_imports: Vec<TypeImport>,
  pub import_equals: Vec<ImportEquals>,
  pub exports: Vec<Export>,
  pub export_as_namespace: Vec<ExportAsNamespace>,
  pub ambient_modules: Vec<AmbientModule>,
}

impl HirFile {
  pub fn module(file_id: FileId) -> Self {
    HirFile {
      file_id,
      module_kind: ModuleKind::Module,
      file_kind: FileKind::Ts,
      decls: Vec::new(),
      imports: Vec::new(),
      type_imports: Vec::new(),
      import_equals: Vec::new(),
      exports: Vec::new(),
      export_as_namespace: Vec::new(),
      ambient_modules: Vec::new(),
    }
  }

  pub fn script(file_id: FileId) -> Self {
    HirFile {
      file_id,
      module_kind: ModuleKind::Script,
      file_kind: FileKind::Ts,
      decls: Vec::new(),
      imports: Vec::new(),
      type_imports: Vec::new(),
      import_equals: Vec::new(),
      exports: Vec::new(),
      export_as_namespace: Vec::new(),
      ambient_modules: Vec::new(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclData {
  pub id: DeclId,
  pub def_id: DefId,
  pub file: FileId,
  pub name: String,
  pub kind: DeclKind,
  pub namespaces: Namespace,
  pub is_ambient: bool,
  pub is_global: bool,
  pub order: u32,
  /// Alias metadata for declarations that create a local binding referencing
  /// another entity (e.g. `import Foo = Bar.Baz`).
  pub alias: Option<AliasTarget>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AliasTarget {
  /// TypeScript `import Foo = Bar.Baz` / `export import Foo = Bar.Baz`.
  EntityName { path: Vec<String>, span: TextRange },
  /// TypeScript `export = Foo` / `export = Foo.Bar` assignments.
  ExportAssignment { path: Vec<String>, span: TextRange },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SymbolOwner {
  Module(FileId),
  Global,
  AmbientModule(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ModuleRef {
  File(FileId),
  Ambient(String),
  Unresolved(String),
}

pub type ImportSource = ModuleRef;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SymbolOrigin {
  Local,
  Import { from: ModuleRef, imported: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolData {
  pub id: SymbolId,
  pub name: String,
  pub namespaces: Namespace,
  pub owner: SymbolOwner,
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

pub trait Resolver {
  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId>;
}

#[derive(Default, Clone, Debug)]
pub struct SymbolTable {
  pub(crate) symbols: BTreeMap<SymbolId, SymbolData>,
  pub(crate) decls: BTreeMap<DeclId, DeclData>,
}

impl SymbolTable {
  /// Number of symbols allocated in this table.
  pub fn symbol_count(&self) -> u32 {
    self.symbols.len() as u32
  }

  pub fn new() -> Self {
    Self::default()
  }

  pub fn symbol(&self, id: SymbolId) -> &SymbolData {
    self.symbols.get(&id).expect("symbol exists for id")
  }

  pub fn symbol_mut(&mut self, id: SymbolId) -> &mut SymbolData {
    self.symbols.get_mut(&id).expect("symbol exists for id")
  }

  pub fn decl(&self, id: DeclId) -> &DeclData {
    self.decls.get(&id).expect("decl exists for id")
  }

  pub fn decl_alias(&self, decl: DeclId) -> Option<&AliasTarget> {
    self.decl(decl).alias.as_ref()
  }

  /// Find the symbol that owns a declaration for the given [`DefId`] in the
  /// requested namespace.
  pub fn symbol_for_def(&self, def: DefId, ns: Namespace) -> Option<SymbolId> {
    for sym in self.symbols.values() {
      if !sym.namespaces.contains(ns) {
        continue;
      }
      if sym
        .decls_for(ns)
        .iter()
        .any(|decl_id| self.decl(*decl_id).def_id == def)
      {
        return Some(sym.id);
      }
    }
    None
  }

  pub fn alloc_decl(
    &mut self,
    file: FileId,
    name: String,
    kind: DeclKind,
    namespaces: Namespace,
    is_ambient: bool,
    is_global: bool,
    order: u32,
    def_id: Option<DefId>,
    alias: Option<AliasTarget>,
  ) -> DeclId {
    let def = def_id.unwrap_or_else(|| synthetic_def_id(file, &name, &kind, order));
    let id = stable_decl_id(file, &name, &kind, namespaces, def, order);
    if let Some(existing) = self.decls.get(&id) {
      debug_assert_eq!(
        existing.alias.as_ref(),
        alias.as_ref(),
        "decl alias mismatch for {:?}",
        id
      );
    } else {
      self.decls.insert(
        id,
        DeclData {
          id,
          def_id: def,
          file,
          name,
          kind,
          namespaces,
          is_ambient,
          is_global,
          order,
          alias,
        },
      );
    }
    id
  }

  pub fn alloc_symbol(
    &mut self,
    owner: &SymbolOwner,
    name: &str,
    namespaces: Namespace,
    origin: SymbolOrigin,
  ) -> SymbolId {
    let id = stable_symbol_id(owner, name, namespaces);
    self.symbols.entry(id).or_insert(SymbolData {
      id,
      name: name.to_string(),
      namespaces,
      owner: owner.clone(),
      decls: Default::default(),
      origin,
    });
    id
  }

  pub fn add_decl_to_symbol(&mut self, symbol: SymbolId, decl: DeclId, namespaces: Namespace) {
    {
      let sym = self.symbol_mut(symbol);
      debug_assert!(
        sym.namespaces.contains(namespaces),
        "symbol namespaces should contain declaration namespaces"
      );
    }

    for bit in namespaces.iter_bits() {
      let mut list = {
        let sym = self.symbol_mut(symbol);
        let list_ref = sym.decls_for_mut(bit);
        list_ref.push(decl);
        std::mem::take(list_ref)
      };
      list.sort_by(|a, b| {
        self
          .decl(*a)
          .order
          .cmp(&self.decl(*b).order)
          .then_with(|| a.cmp(b))
      });
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
  pub(crate) module_symbols: BTreeMap<FileId, SymbolGroups>,
  pub(crate) module_exports: BTreeMap<FileId, ExportMap>,
  pub(crate) global_symbols: BTreeMap<String, SymbolGroup>,
  pub(crate) ambient_module_symbols: BTreeMap<String, SymbolGroups>,
  pub(crate) ambient_module_exports: BTreeMap<String, ExportMap>,
  pub(crate) def_to_symbol: BTreeMap<(DefId, Namespace), SymbolId>,
}

impl TsProgramSemantics {
  pub fn empty() -> Self {
    TsProgramSemantics {
      symbols: SymbolTable::new(),
      module_symbols: BTreeMap::new(),
      module_exports: BTreeMap::new(),
      global_symbols: BTreeMap::new(),
      ambient_module_symbols: BTreeMap::new(),
      ambient_module_exports: BTreeMap::new(),
      def_to_symbol: BTreeMap::new(),
    }
  }

  pub fn exports_of(&self, file: FileId) -> &ExportMap {
    self
      .module_exports
      .get(&file)
      .expect("exports available for file")
  }

  pub fn exports_of_opt(&self, file: FileId) -> Option<&ExportMap> {
    self.module_exports.get(&file)
  }

  pub fn symbols(&self) -> &SymbolTable {
    &self.symbols
  }

  /// Resolve a name within the lexical scope of a module (including imports).
  /// Returns the symbol for the requested namespace, if present.
  pub fn resolve_in_module(&self, file: FileId, name: &str, ns: Namespace) -> Option<SymbolId> {
    let module = self.module_symbols.get(&file)?;
    let group = module.get(name)?;
    group.symbol_for(ns, &self.symbols)
  }

  /// Resolve an exported name from a module to the canonical symbol for the
  /// requested namespace. Export maps are deterministic and cycle-safe.
  pub fn resolve_export(&self, file: FileId, name: &str, ns: Namespace) -> Option<SymbolId> {
    let exports = self.module_exports.get(&file)?;
    let group = exports.get(name)?;
    group.symbol_for(ns, &self.symbols)
  }

  /// Returns the declarations that participate in a symbol's namespace in
  /// deterministic order (by binder visit order).
  pub fn symbol_decls(&self, symbol: SymbolId, ns: Namespace) -> &[DeclId] {
    let sym = self.symbols.symbol(symbol);
    if !ns.is_single() || !sym.namespaces.contains(ns) {
      return &[];
    }
    sym.decls_for(ns).as_slice()
  }

  pub fn decl_alias(&self, decl: DeclId) -> Option<&AliasTarget> {
    self.symbols.decl_alias(decl)
  }

  pub fn symbol_alias_target(&self, symbol: SymbolId, ns: Namespace) -> Option<&AliasTarget> {
    let sym = self.symbols.symbol(symbol);
    if !ns.is_single() || !sym.namespaces.contains(ns) {
      return None;
    }
    sym
      .decls_for(ns)
      .iter()
      .find_map(|decl| self.symbols.decl_alias(*decl))
  }

  pub fn global_symbols(&self) -> &BTreeMap<String, SymbolGroup> {
    &self.global_symbols
  }

  pub fn ambient_module_symbols(&self) -> &BTreeMap<String, SymbolGroups> {
    &self.ambient_module_symbols
  }

  pub fn ambient_module_exports(&self) -> &BTreeMap<String, ExportMap> {
    &self.ambient_module_exports
  }

  pub fn exports_of_ambient_module(&self, specifier: &str) -> Option<&ExportMap> {
    self.ambient_module_exports.get(specifier)
  }

  /// Look up the canonical symbol containing the provided HIR declaration.
  pub fn symbol_for_def(&self, def: DefId, ns: Namespace) -> Option<SymbolId> {
    if !ns.is_single() {
      return None;
    }
    self.def_to_symbol.get(&(def, ns)).copied()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ImportEntry {
  pub local: String,
  pub from: ModuleRef,
  pub imported: ImportItem,
  pub type_only: bool,
  pub def_id: Option<DefId>,
  pub local_span: TextRange,
  pub specifier_span: Span,
  pub symbol: SymbolId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ImportItem {
  Named(String),
  Default,
  Namespace,
}

pub(crate) type SymbolGroups = BTreeMap<String, SymbolGroup>;
