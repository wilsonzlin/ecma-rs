use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  lower_file_with_diagnostics, ExportDefaultValue, ExportKind, ExprKind, FileKind as HirFileKind,
  LowerResult, ObjectProperty, StmtKind,
};
use semantic_js::ts as sem_ts;
use types_ts_interned::PrimitiveIds;

use crate::db::inputs::{
  CancellationToken, CancelledInput, CompilerOptionsInput, FileInput, ModuleResolutionInput,
  RootsInput,
};
use crate::db::{Db, ModuleKey};
use crate::lib_support::{CompilerOptions, FileKind};
use crate::codes;
use crate::profile::QueryKind;
use crate::queries::parse as parser;
use crate::sem_hir::sem_hir_from_lower;
use crate::semantic_js::SymbolId;
use crate::symbols::SymbolBinding;
use crate::FileKey;
use crate::{BodyId, DefId, TypeId};

fn file_id_from_key(db: &dyn Db, key: &FileKey) -> FileId {
  db.file_input_by_key(key)
    .unwrap_or_else(|| panic!("file {:?} must be seeded before use", key))
    .file_id(db)
}

#[salsa::tracked]
fn compiler_options_for(db: &dyn Db, handle: CompilerOptionsInput) -> CompilerOptions {
  handle.options(db)
}

#[salsa::tracked]
fn roots_for(db: &dyn Db, handle: RootsInput) -> Arc<[FileKey]> {
  handle.roots(db)
}

#[salsa::tracked]
fn cancellation_token_for(db: &dyn Db, handle: CancelledInput) -> CancellationToken {
  handle.token(db)
}

#[salsa::tracked]
fn file_kind_for(db: &dyn Db, file: FileInput) -> FileKind {
  file.kind(db)
}

#[salsa::tracked]
fn file_text_for(db: &dyn Db, file: FileInput) -> Arc<str> {
  file.text(db)
}

#[salsa::tracked]
fn module_resolve_for(db: &dyn Db, entry: ModuleResolutionInput) -> Option<FileId> {
  entry.resolved(db)
}

#[salsa::tracked]
fn module_specifiers_for(db: &dyn Db, file: FileInput) -> Arc<[Arc<str>]> {
  let lowered = lower_hir_for(db, file);
  let Some(lowered) = lowered.lowered.as_deref() else {
    return Arc::from([]);
  };
  let mut specs: Vec<_> = collect_module_specifiers(lowered)
    .into_iter()
    .map(|(spec, _)| spec)
    .collect();
  specs.sort_unstable_by(|a, b| a.as_ref().cmp(b.as_ref()));
  specs.dedup();
  Arc::from(specs.into_boxed_slice())
}

#[salsa::tracked]
fn module_deps_for(db: &dyn Db, file: FileInput) -> Arc<[FileId]> {
  let specs = module_specifiers_for(db, file);
  let mut deps = Vec::new();
  for spec in specs.iter() {
    if let Some(target) = module_resolve(db, file.file_id(db), Arc::clone(spec)) {
      deps.push(target);
    }
  }
  deps.sort_by_key(|id| id.0);
  deps.dedup();
  Arc::from(deps.into_boxed_slice())
}

#[salsa::tracked]
fn module_dep_diagnostics_for(db: &dyn Db, file: FileInput) -> Arc<[Diagnostic]> {
  let specs = module_specifiers_for(db, file);
  let lowered = lower_hir_for(db, file);
  let Some(lowered) = lowered.lowered.as_deref() else {
    return Arc::from([]);
  };
  let mut spans = HashMap::new();
  for (spec, span) in collect_module_specifiers(lowered).into_iter() {
    spans.entry(spec).or_insert(span);
  }

  let mut diagnostics = Vec::new();
  for spec in specs.iter() {
    if module_resolve(db, file.file_id(db), Arc::clone(spec)).is_none() {
      if let Some(span) = spans.get(spec) {
        diagnostics.push(codes::UNRESOLVED_MODULE.error(
          format!("module {} could not be resolved", spec),
          Span::new(file.file_id(db), *span),
        ));
      }
    }
  }
  diagnostics.sort();
  diagnostics.dedup();
  Arc::from(diagnostics.into_boxed_slice())
}

#[derive(Debug, Clone)]
pub struct LowerResultWithDiagnostics {
  pub lowered: Option<Arc<LowerResult>>,
  pub diagnostics: Vec<Diagnostic>,
  pub file_kind: FileKind,
}

impl PartialEq for LowerResultWithDiagnostics {
  fn eq(&self, other: &Self) -> bool {
    let lowered_eq = match (&self.lowered, &other.lowered) {
      (Some(left), Some(right)) => Arc::ptr_eq(left, right),
      (None, None) => true,
      _ => false,
    };
    lowered_eq && self.diagnostics == other.diagnostics && self.file_kind == other.file_kind
  }
}

/// Minimal interface required to compute global bindings.
pub trait GlobalBindingsDb {
  /// Bound TS semantics for the current program.
  fn ts_semantics(&self) -> Option<Arc<sem_ts::TsProgramSemantics>>;
  /// Value namespace bindings introduced by `.d.ts` files.
  fn dts_value_bindings(&self) -> Vec<(String, SymbolBinding)>;
  /// Canonical type for a definition, if already computed.
  fn type_of_def(&self, def: DefId) -> Option<TypeId>;
  /// Primitive type identifiers from the shared type store.
  fn primitive_ids(&self) -> Option<PrimitiveIds>;
}

fn deterministic_symbol_id(name: &str) -> SymbolId {
  // FNV-1a 64-bit with fold-down to `u32` for stability across runs.
  let mut hash: u64 = 0xcbf29ce484222325;
  for byte in name.as_bytes() {
    hash ^= *byte as u64;
    hash = hash.wrapping_mul(0x100000001b3);
  }
  let folded = hash ^ (hash >> 32);
  SymbolId(folded as u32)
}

/// Global value bindings derived from TS semantics, `.d.ts` files, and builtin
/// symbols. This intentionally returns a sorted map to keep iteration
/// deterministic regardless of evaluation order.
pub fn global_bindings(db: &dyn GlobalBindingsDb) -> Arc<BTreeMap<String, SymbolBinding>> {
  let mut globals: BTreeMap<String, SymbolBinding> = BTreeMap::new();
  let semantics = db.ts_semantics();

  if let Some(sem) = semantics.as_deref() {
    let symbols = sem.symbols();
    for (name, group) in sem.global_symbols() {
      if let Some(symbol) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) {
        let def = symbols
          .symbol(symbol)
          .decls_for(sem_ts::Namespace::VALUE)
          .first()
          .map(|decl| symbols.decl(*decl).def_id);
        let type_id = def.and_then(|def| db.type_of_def(def));
        globals.insert(
          name.clone(),
          SymbolBinding {
            symbol: symbol.into(),
            def,
            type_id,
          },
        );
      }
    }
  }

  for (name, mut binding) in db.dts_value_bindings().into_iter() {
    if let Some(def) = binding.def {
      if binding.type_id.is_none() {
        binding.type_id = db.type_of_def(def);
      }
      if let Some(sem) = semantics.as_deref() {
        if let Some(symbol) = sem.symbol_for_def(def, sem_ts::Namespace::VALUE) {
          binding.symbol = symbol.into();
        }
      }
    }

    globals
      .entry(name.clone())
      .and_modify(|existing| {
        if existing.type_id.is_none() {
          existing.type_id = binding.type_id;
        }
        if existing.def.is_none() {
          existing.def = binding.def;
        }
      })
      .or_insert(binding);
  }

  let primitives = db.primitive_ids();
  globals
    .entry("undefined".to_string())
    .or_insert(SymbolBinding {
      symbol: deterministic_symbol_id("undefined"),
      def: None,
      type_id: primitives.map(|p| p.undefined),
    });
  globals.entry("Error".to_string()).or_insert(SymbolBinding {
    symbol: deterministic_symbol_id("Error"),
    def: None,
    type_id: primitives.map(|p| p.any),
  });

  Arc::new(globals)
}

impl Eq for LowerResultWithDiagnostics {}

static PARSE_QUERY_CALLS: AtomicUsize = AtomicUsize::new(0);

pub fn parse_query_count() -> usize {
  PARSE_QUERY_CALLS.load(Ordering::Relaxed)
}

pub fn reset_parse_query_count() {
  PARSE_QUERY_CALLS.store(0, Ordering::Relaxed);
}

#[salsa::tracked]
fn parse_for(db: &dyn Db, file: FileInput) -> parser::ParseResult {
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::Parse, false));
  PARSE_QUERY_CALLS.fetch_add(1, Ordering::Relaxed);
  let kind = file.kind(db);
  let source = file.text(db);
  parser::parse(file.file_id(db), kind, &source)
}

#[salsa::tracked]
fn lower_hir_for(db: &dyn Db, file: FileInput) -> LowerResultWithDiagnostics {
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::LowerHir, false));
  let parsed = parse_for(db, file);
  let file_kind = file.kind(db);
  let mut diagnostics = parsed.diagnostics.clone();
  let lowered = parsed.ast.as_ref().map(|ast| {
    let (lowered, mut lower_diags) =
      lower_file_with_diagnostics(file.file_id(db), map_hir_file_kind(file_kind), ast);
    diagnostics.append(&mut lower_diags);
    Arc::new(lowered)
  });

  LowerResultWithDiagnostics {
    lowered,
    diagnostics,
    file_kind,
  }
}

#[salsa::tracked]
fn sem_hir_for(db: &dyn Db, file: FileInput) -> sem_ts::HirFile {
  let lowered = lower_hir_for(db, file);
  if let Some(lowered) = lowered.lowered.as_ref() {
    sem_hir_from_lower(lowered)
  } else {
    empty_sem_hir(file.file_id(db), lowered.file_kind)
  }
}

fn empty_sem_hir(file: FileId, kind: FileKind) -> sem_ts::HirFile {
  sem_ts::HirFile {
    file_id: sem_ts::FileId(file.0),
    module_kind: sem_ts::ModuleKind::Script,
    file_kind: match kind {
      FileKind::Dts => sem_ts::FileKind::Dts,
      FileKind::Js | FileKind::Ts | FileKind::Tsx | FileKind::Jsx => sem_ts::FileKind::Ts,
    },
    decls: Vec::new(),
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  }
}

fn map_hir_file_kind(kind: FileKind) -> HirFileKind {
  match kind {
    FileKind::Dts => HirFileKind::Dts,
    FileKind::Js => HirFileKind::Js,
    FileKind::Ts => HirFileKind::Ts,
    FileKind::Tsx => HirFileKind::Tsx,
    FileKind::Jsx => HirFileKind::Jsx,
  }
}

#[derive(Clone)]
pub struct TsSemantics {
  pub semantics: Arc<sem_ts::TsProgramSemantics>,
  pub diagnostics: Arc<Vec<Diagnostic>>,
}

impl PartialEq for TsSemantics {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.semantics, &other.semantics) && self.diagnostics == other.diagnostics
  }
}

impl Eq for TsSemantics {}

impl std::fmt::Debug for TsSemantics {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TsSemantics")
      .field("semantics", &self.semantics)
      .field("diagnostics", &self.diagnostics)
      .finish()
  }
}

#[salsa::tracked]
fn all_files_for(db: &dyn Db) -> Arc<Vec<FileId>> {
  let mut visited = BTreeSet::new();
  let mut queue: VecDeque<FileId> = db
    .roots_input()
    .roots(db)
    .iter()
    .map(|key| file_id_from_key(db, key))
    .collect();
  while let Some(file) = queue.pop_front() {
    if !visited.insert(file) {
      continue;
    }
    queue.extend(
      module_deps_for(db, db.file_input(file).expect("file seeded for deps"))
        .iter()
        .copied(),
    );
  }
  Arc::new(visited.into_iter().collect())
}

#[salsa::tracked]
fn ts_semantics_for(db: &dyn Db) -> Arc<TsSemantics> {
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::Bind, false));
  let files = all_files_for(db);
  let mut diagnostics = Vec::new();
  let mut sem_hirs: HashMap<sem_ts::FileId, Arc<sem_ts::HirFile>> = HashMap::new();
  for file in files.iter() {
    let lowered = lower_hir_for(db, db.file_input(*file).expect("file seeded for lowering"));
    diagnostics.extend(lowered.diagnostics.iter().cloned());
    sem_hirs.insert(
      sem_ts::FileId(file.0),
      Arc::new(sem_hir_for(
        db,
        db.file_input(*file).expect("file seeded for sem hir"),
      )),
    );
  }

  let mut roots: Vec<_> = db
    .roots_input()
    .roots(db)
    .iter()
    .map(|f| file_id_from_key(db, f))
    .map(|id| sem_ts::FileId(id.0))
    .collect();
  roots.sort();
  roots.dedup();
  let resolver = DbResolver { db };
  let (semantics, mut bind_diags) = sem_ts::bind_ts_program(&roots, &resolver, |file| {
    sem_hirs.get(&file).cloned().unwrap_or_else(|| {
      Arc::new(empty_sem_hir(
        FileId(file.0),
        db.file_input(FileId(file.0))
          .map(|input| input.kind(db))
          .unwrap_or(FileKind::Ts),
      ))
    })
  });
  diagnostics.append(&mut bind_diags);
  diagnostics.sort();
  diagnostics.dedup();
  Arc::new(TsSemantics {
    semantics: Arc::new(semantics),
    diagnostics: Arc::new(diagnostics),
  })
}

struct DbResolver<'db> {
  db: &'db dyn Db,
}

impl<'db> sem_ts::Resolver for DbResolver<'db> {
  fn resolve(&self, from: sem_ts::FileId, specifier: &str) -> Option<sem_ts::FileId> {
    module_resolve(self.db, FileId(from.0), Arc::<str>::from(specifier))
      .map(|id| sem_ts::FileId(id.0))
  }
}

fn collect_module_specifiers(lowered: &hir_js::LowerResult) -> Vec<(Arc<str>, TextRange)> {
  let mut specs = Vec::new();
  for import in lowered.hir.imports.iter() {
    match &import.kind {
      hir_js::ImportKind::Es(es) => {
        specs.push((Arc::from(es.specifier.value.clone()), es.specifier.span));
      }
      hir_js::ImportKind::ImportEquals(eq) => {
        if let hir_js::ImportEqualsTarget::Module(module) = &eq.target {
          specs.push((Arc::from(module.value.clone()), module.span));
        }
      }
    }
  }
  for export in lowered.hir.exports.iter() {
    match &export.kind {
      ExportKind::Named(named) => {
        if let Some(source) = named.source.as_ref() {
          specs.push((Arc::from(source.value.clone()), source.span));
        }
      }
      ExportKind::ExportAll(all) => {
        specs.push((Arc::from(all.source.value.clone()), all.source.span));
      }
      _ => {}
    }
  }
  for ty in lowered.types.type_exprs.iter() {
    if let hir_js::TypeExprKind::Import(import) = &ty.kind {
      specs.push((Arc::from(import.module.clone()), ty.span));
    }
  }
  specs
}

/// Current compiler options.
pub fn compiler_options(db: &dyn Db) -> CompilerOptions {
  compiler_options_for(db, db.compiler_options_input())
}

/// Entry-point file roots selected by the host.
pub fn roots(db: &dyn Db) -> Arc<[FileKey]> {
  roots_for(db, db.roots_input())
}

/// Cancellation token to propagate through long-running queries.
pub fn cancelled(db: &dyn Db) -> Arc<AtomicBool> {
  cancellation_token_for(db, db.cancelled_input()).0.clone()
}

/// File kind for a given file identifier.
pub fn file_kind(db: &dyn Db, file: FileId) -> FileKind {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before reading kind");
  file_kind_for(db, handle)
}

/// Source text for a given file identifier.
pub fn file_text(db: &dyn Db, file: FileId) -> Arc<str> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before reading text");
  file_text_for(db, handle)
}

pub fn parse(db: &dyn Db, file: FileId) -> parser::ParseResult {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before parsing");
  parse_for(db, handle)
}

pub fn lower_hir(db: &dyn Db, file: FileId) -> LowerResultWithDiagnostics {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before lowering");
  lower_hir_for(db, handle)
}

pub fn module_specifiers(db: &dyn Db, file: FileId) -> Arc<[Arc<str>]> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before querying module specifiers");
  module_specifiers_for(db, handle)
}

pub fn module_deps(db: &dyn Db, file: FileId) -> Arc<[FileId]> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before querying module deps");
  module_deps_for(db, handle)
}

pub fn module_dep_diagnostics(db: &dyn Db, file: FileId) -> Arc<[Diagnostic]> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before querying module deps");
  module_dep_diagnostics_for(db, handle)
}

pub fn reachable_files(db: &dyn Db) -> Arc<Vec<FileId>> {
  all_files_for(db)
}

pub fn sem_hir(db: &dyn Db, file: FileId) -> sem_ts::HirFile {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before computing sem HIR");
  sem_hir_for(db, handle)
}

/// Host-provided module resolution result.
pub fn module_resolve(db: &dyn Db, from: FileId, specifier: Arc<str>) -> Option<FileId> {
  let key = ModuleKey::new(from, specifier);
  db.module_resolution_input(&key)
    .and_then(|input| module_resolve_for(db, input))
}

pub fn all_files(db: &dyn Db) -> Arc<Vec<FileId>> {
  all_files_for(db)
}

pub fn ts_semantics(db: &dyn Db) -> Arc<TsSemantics> {
  ts_semantics_for(db)
}

/// Expose the current revision for smoke-testing the salsa plumbing.
#[salsa::tracked]
pub fn db_revision(db: &dyn Db) -> salsa::Revision {
  salsa::plumbing::current_revision(db)
}

#[salsa::tracked]
fn def_to_file_for(db: &dyn Db) -> Arc<BTreeMap<DefId, FileId>> {
  let mut files: Vec<_> = all_files(db).iter().copied().collect();
  files.sort_by_key(|f| f.0);

  let mut map = BTreeMap::new();
  for file in files {
    let lowered = lower_hir(db, file);
    if let Some(lowered) = lowered.lowered.as_ref() {
      for def in lowered.defs.iter() {
        if let Some(existing) = map.insert(def.id, file) {
          debug_assert_eq!(
            existing, file,
            "definition {def:?} seen in multiple files: {existing:?} and {file:?}"
          );
        }
      }
    }
  }

  Arc::new(map)
}

/// Map every [`DefId`] in the program to its owning [`FileId`].
///
/// Files are processed in ascending [`FileId`] order to keep iteration
/// deterministic regardless of the order returned by [`all_files`].
pub fn def_to_file(db: &dyn Db) -> Arc<BTreeMap<DefId, FileId>> {
  def_to_file_for(db)
}

#[salsa::tracked]
fn body_to_file_for(db: &dyn Db) -> Arc<BTreeMap<BodyId, FileId>> {
  let mut files: Vec<_> = all_files(db).iter().copied().collect();
  files.sort_by_key(|f| f.0);

  let mut map = BTreeMap::new();
  for file in files {
    let lowered = lower_hir(db, file);
    if let Some(lowered) = lowered.lowered.as_ref() {
      for body_id in lowered.body_index.keys() {
        if let Some(existing) = map.insert(*body_id, file) {
          debug_assert_eq!(
            existing, file,
            "body {body_id:?} seen in multiple files: {existing:?} and {file:?}"
          );
        }
      }
    }
  }

  Arc::new(map)
}

/// Map every [`BodyId`] in the program to its owning [`FileId`].
///
/// Files are processed in ascending [`FileId`] order to guarantee deterministic
/// results even if the root list is shuffled.
pub fn body_to_file(db: &dyn Db) -> Arc<BTreeMap<BodyId, FileId>> {
  body_to_file_for(db)
}

fn record_parent(map: &mut BTreeMap<BodyId, BodyId>, child: BodyId, parent: BodyId) {
  if let Some(existing) = map.get(&child) {
    debug_assert_eq!(
      *existing, parent,
      "conflicting parents for {child:?}: {existing:?} vs {parent:?}"
    );
    return;
  }
  map.insert(child, parent);
}

#[salsa::tracked]
fn body_parents_in_file_for(db: &dyn Db, file: FileInput) -> Arc<BTreeMap<BodyId, BodyId>> {
  let file_id = file.file_id(db);
  let lowered = lower_hir(db, file_id);
  let Some(lowered) = lowered.lowered.as_ref() else {
    return Arc::new(BTreeMap::new());
  };
  let mut parents = BTreeMap::new();

  let mut body_ids: Vec<_> = lowered.body_index.keys().copied().collect();
  body_ids.sort_by_key(|id| id.0);

  for body_id in body_ids {
    let Some(body) = lowered.body(body_id) else {
      continue;
    };

    for stmt in body.stmts.iter() {
      if let StmtKind::Decl(def_id) = stmt.kind {
        if let Some(def) = lowered.def(def_id) {
          if let Some(child_body) = def.body {
            record_parent(&mut parents, child_body, body_id);
          }
        }
      }
    }

    for expr in body.exprs.iter() {
      match &expr.kind {
        ExprKind::FunctionExpr { body: child, .. } => record_parent(&mut parents, *child, body_id),
        ExprKind::ClassExpr { body: child, .. } => record_parent(&mut parents, *child, body_id),
        ExprKind::Object(object) => {
          for prop in object.properties.iter() {
            match prop {
              ObjectProperty::Getter { body: child, .. }
              | ObjectProperty::Setter { body: child, .. } => {
                record_parent(&mut parents, *child, body_id)
              }
              _ => {}
            }
          }
        }
        _ => {}
      }
    }
  }

  let root_body = lowered.hir.root_body;
  for export in lowered.hir.exports.iter() {
    match &export.kind {
      ExportKind::Default(default) => match &default.value {
        ExportDefaultValue::Expr { body, .. }
        | ExportDefaultValue::Class { body, .. }
        | ExportDefaultValue::Function { body, .. } => {
          record_parent(&mut parents, *body, root_body)
        }
      },
      ExportKind::Assignment(assign) => record_parent(&mut parents, assign.body, root_body),
      _ => {}
    }
  }

  Arc::new(parents)
}

/// Parent map for all bodies declared within a single file.
///
/// A child relationship is recorded when a body is owned by a declaration within
/// another body (`StmtKind::Decl`) or created by a function/class expression.
/// Default export bodies are also associated with the file's top-level body to
/// keep traversal cycle-safe.
pub fn body_parents_in_file(db: &dyn Db, file: FileId) -> Arc<BTreeMap<BodyId, BodyId>> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before computing parents");
  body_parents_in_file_for(db, handle)
}

/// Owning file for a definition, if present in the index.
pub fn def_file(db: &dyn Db, def: DefId) -> Option<FileId> {
  def_to_file(db).get(&def).copied()
}

/// Owning file for a body, if present in the index.
pub fn body_file(db: &dyn Db, body: BodyId) -> Option<FileId> {
  body_to_file(db).get(&body).copied()
}

/// Parent body for the given body.
pub fn body_parent(db: &dyn Db, body: BodyId) -> Option<BodyId> {
  let file = body_file(db, body)?;
  body_parents_in_file(db, file).get(&body).copied()
}
