use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;
use std::panic::panic_any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ahash::{AHashMap, AHashSet};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  lower_file_with_diagnostics_with_cancellation, DefKind, ExportDefaultValue, ExportKind, ExprKind,
  FileKind as HirFileKind, LowerResult, ObjectProperty, PatId, PatKind, StmtKind, VarDeclKind,
};
use parse_js::error::SyntaxErrorType;
use parse_js::{parse_with_options_cancellable, Dialect, ParseOptions, SourceType};
use semantic_js::ts as sem_ts;
use types_ts_interned::{CacheStats, PrimitiveIds, TypeStore};

use crate::codes;
use crate::db::cache::{BodyCache, DefCache};
use crate::db::inputs::{
  CancellationToken, CancelledInput, CompilerOptionsInput, FileInput, ModuleResolutionInput,
  RootsInput,
};
use crate::db::spans::{expr_at_from_spans, FileSpanIndex};
use crate::db::symbols::{LocalSymbolInfo, SymbolIndex};
use crate::db::{symbols, Db};
use crate::lib_support::{CacheOptions, CompilerOptions, FileKind};
use crate::lower_metrics;
use crate::parse_metrics;
use crate::profile::{CacheKind, QueryKind, QueryStatsCollector};
use crate::queries::parse as parser;
use crate::symbols::{semantic_js::SymbolId, SymbolBinding, SymbolOccurrence};
use crate::triple_slash::{
  normalize_reference_path_specifier, scan_triple_slash_directives, TripleSlashReferenceKind,
};
use crate::FileKey;
use crate::{BodyId, DefId, ExprId, TypeId};
use salsa::plumbing::current_revision;
use salsa::Setter;

fn cache_delta(after: &CacheStats, before: &CacheStats) -> CacheStats {
  CacheStats {
    hits: after.hits.saturating_sub(before.hits),
    misses: after.misses.saturating_sub(before.misses),
    insertions: after.insertions.saturating_sub(before.insertions),
    evictions: after.evictions.saturating_sub(before.evictions),
  }
}

fn file_id_from_key(db: &dyn Db, key: &FileKey) -> Option<FileId> {
  db.file_input_by_key(key).map(|input| input.file_id(db))
}

fn panic_if_cancelled(db: &dyn Db) {
  if cancelled(db).load(Ordering::Relaxed) {
    panic_any(crate::FatalError::Cancelled);
  }
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
  panic_if_cancelled(db);
  let lowered = lower_hir_for(db, file);
  let parsed = parse_for(db, file);
  let source = file_text_for(db, file);
  let triple_slash = scan_triple_slash_directives(source.as_ref());
  let mut specs: Vec<Arc<str>> = Vec::new();
  if let Some(lowered) = lowered.lowered.as_deref() {
    specs.reserve(lowered.hir.imports.len() + lowered.hir.exports.len());
    collect_module_specifiers(lowered, &mut specs);
  }
  if let Some(ast) = parsed.ast.as_deref() {
    collect_type_only_module_specifier_values_from_ast(ast, &mut specs);
    collect_module_augmentation_specifier_values_from_ast(ast, &mut specs);
  }
  for reference in triple_slash.references.iter() {
    let value = reference.value(source.as_ref());
    if value.is_empty() {
      continue;
    }
    match reference.kind {
      TripleSlashReferenceKind::Path => {
        let normalized = normalize_reference_path_specifier(value);
        specs.push(Arc::<str>::from(normalized.as_ref()));
      }
      TripleSlashReferenceKind::Types => specs.push(Arc::<str>::from(value)),
      TripleSlashReferenceKind::Lib => {}
    }
  }
  specs.sort_unstable_by(|a, b| a.as_ref().cmp(b.as_ref()));
  specs.dedup();
  Arc::from(specs.into_boxed_slice())
}

#[salsa::tracked]
fn module_deps_for(db: &dyn Db, file: FileInput) -> Arc<[FileId]> {
  panic_if_cancelled(db);
  let specs = module_specifiers_for(db, file);
  let mut deps = Vec::with_capacity(specs.len());
  for spec in specs.iter() {
    panic_if_cancelled(db);
    if let Some(target) = module_resolve_ref(db, file.file_id(db), spec.as_ref()) {
      deps.push(target);
    }
  }
  deps.sort_unstable_by_key(|id| id.0);
  deps.dedup();
  Arc::from(deps.into_boxed_slice())
}

#[salsa::tracked]
fn module_dep_diagnostics_for(db: &dyn Db, file: FileInput) -> Arc<[Diagnostic]> {
  panic_if_cancelled(db);
  unresolved_module_diagnostics_for(db, file)
}

#[salsa::tracked]
fn unresolved_module_diagnostics_for(db: &dyn Db, file: FileInput) -> Arc<[Diagnostic]> {
  panic_if_cancelled(db);
  let lowered = lower_hir_for(db, file);
  let Some(lowered) = lowered.lowered.as_deref() else {
    return Arc::from([]);
  };
  let semantics = ts_semantics(db);
  let mut diagnostics = Vec::new();
  let file_id = file.file_id(db);
  let source = file_text_for(db, file);
  struct UnresolvedModuleChecker<'a> {
    db: &'a dyn Db,
    file_id: FileId,
    semantics: &'a TsSemantics,
    source: &'a str,
    seen: AHashSet<(u32, u32, &'a str)>,
  }

  impl<'a> UnresolvedModuleChecker<'a> {
    fn refine_span(&self, span: TextRange, value: &str) -> TextRange {
      if (span.end as usize) <= self.source.len() {
        if let Some(segment) = self.source.get(span.start as usize..span.end as usize) {
          for quote in ['"', '\'', '`'] {
            let needle = format!("{quote}{value}{quote}");
            if let Some(idx) = segment.find(&needle) {
              let start = span.start + idx as u32;
              let end = start + needle.len() as u32;
              return TextRange::new(start, end);
            }
          }
        }
      }
      span
    }

    fn emit_unresolved(
      &mut self,
      specifier: &'a str,
      span: TextRange,
      diags: &mut Vec<Diagnostic>,
    ) {
      if self
        .semantics
        .semantics
        .exports_of_ambient_module(specifier)
        .is_some()
      {
        return;
      }

      let range = self.refine_span(span, specifier);
      let key = (range.start, range.end, specifier);
      if !self.seen.insert(key) {
        return;
      }

      let mut diag = codes::UNRESOLVED_MODULE.error(
        format!("unresolved module specifier \"{specifier}\""),
        Span::new(self.file_id, range),
      );
      diag.push_note(format!("module specifier: \"{specifier}\""));
      diags.push(diag);
    }

    fn check_value(&mut self, specifier: &'a str, span: TextRange, diags: &mut Vec<Diagnostic>) {
      if module_resolve_ref(self.db, self.file_id, specifier).is_some() {
        return;
      }
      self.emit_unresolved(specifier, span, diags);
    }

    fn check_specifier(&mut self, spec: &'a hir_js::ModuleSpecifier, diags: &mut Vec<Diagnostic>) {
      self.check_value(spec.value.as_str(), spec.span, diags);
    }
  }

  {
    let mut checker = UnresolvedModuleChecker {
      db,
      file_id,
      semantics: semantics.as_ref(),
      source: source.as_ref(),
      seen: AHashSet::new(),
    };

    for import in lowered.hir.imports.iter() {
      match &import.kind {
        hir_js::ImportKind::Es(es) => {
          checker.check_specifier(&es.specifier, &mut diagnostics);
        }
        hir_js::ImportKind::ImportEquals(eq) => {
          if let hir_js::ImportEqualsTarget::Module(module) = &eq.target {
            checker.check_specifier(module, &mut diagnostics);
          }
        }
      }
    }

    for export in lowered.hir.exports.iter() {
      match &export.kind {
        ExportKind::Named(named) => {
          if let Some(source) = named.source.as_ref() {
            checker.check_specifier(source, &mut diagnostics);
          }
        }
        ExportKind::ExportAll(all) => {
          checker.check_specifier(&all.source, &mut diagnostics);
        }
        ExportKind::Default(_) | ExportKind::Assignment(_) | ExportKind::AsNamespace(_) => {}
      }
    }

    for arenas in lowered.types.values() {
      for ty in arenas.type_exprs.iter() {
        match &ty.kind {
          hir_js::TypeExprKind::TypeRef(type_ref) => {
            if let hir_js::TypeName::Import(import) = &type_ref.name {
              if let Some(module) = import.module.as_deref() {
                checker.check_value(module, ty.span, &mut diagnostics);
              }
            }
          }
          hir_js::TypeExprKind::TypeQuery(name) => {
            if let hir_js::TypeName::Import(import) = name {
              if let Some(module) = import.module.as_deref() {
                checker.check_value(module, ty.span, &mut diagnostics);
              }
            }
          }
          hir_js::TypeExprKind::Import(import) => {
            checker.check_value(import.module.as_str(), ty.span, &mut diagnostics);
          }
          _ => {}
        }
      }
    }

    if let Some(ast) = parse_for(db, file).ast.as_deref() {
      if ast_has_module_syntax(ast) {
        use parse_js::ast::node::Node;
        use parse_js::ast::stmt::Stmt;
        use parse_js::ast::ts_stmt::ModuleName;
        use parse_js::loc::Loc;

        fn to_range(loc: Loc) -> TextRange {
          TextRange::new(loc.start_u32(), loc.end_u32())
        }

        fn walk<'a>(
          stmts: &'a [Node<Stmt>],
          checker: &mut UnresolvedModuleChecker<'a>,
          diags: &mut Vec<Diagnostic>,
        ) {
          for stmt in stmts {
            match stmt.stx.as_ref() {
              Stmt::ModuleDecl(module) => {
                if let ModuleName::String(spec) = &module.stx.name {
                  checker.check_value(spec.as_str(), to_range(module.stx.name_loc), diags);
                }
              }
              Stmt::GlobalDecl(global) => {
                walk(&global.stx.body, checker, diags);
              }
              _ => {}
            }
          }
        }

        walk(&ast.stx.body, &mut checker, &mut diagnostics);
      }
    }
  }

  diagnostics.sort_by(|a, b| {
    a.primary
      .range
      .start
      .cmp(&b.primary.range.start)
      .then_with(|| a.primary.range.end.cmp(&b.primary.range.end))
      .then_with(|| a.code.as_str().cmp(b.code.as_str()))
      .then_with(|| a.message.cmp(&b.message))
  });
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
  // FNV-1a 64-bit with fold-down to keep outputs stable across runs.
  let mut hash: u64 = 0xcbf29ce484222325;
  for byte in name.as_bytes() {
    hash ^= *byte as u64;
    hash = hash.wrapping_mul(0x100000001b3);
  }
  let folded = hash ^ (hash >> 32);
  SymbolId(folded)
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

  // Ensure a minimal set of JS builtins exist even when no lib files are loaded.
  //
  // These should be stable, deterministic, and should not depend on declaration
  // ordering from `.d.ts` inputs. When a declaration exists we preserve its
  // `symbol`/`def` identity but prefer our canonical primitive type IDs so that
  // downstream queries (and tests) see the expected types.
  if let Some(primitives) = db.primitive_ids() {
    globals
      .entry("undefined".to_string())
      .and_modify(|binding| binding.type_id = Some(primitives.undefined))
      .or_insert(SymbolBinding {
        symbol: deterministic_symbol_id("undefined"),
        def: None,
        type_id: Some(primitives.undefined),
      });
    globals
      .entry("Error".to_string())
      .and_modify(|binding| {
        if binding.type_id.is_none() {
          binding.type_id = Some(primitives.any);
        }
      })
      .or_insert(SymbolBinding {
        symbol: deterministic_symbol_id("Error"),
        def: None,
        type_id: Some(primitives.any),
      });
  } else {
    globals
      .entry("undefined".to_string())
      .or_insert(SymbolBinding {
        symbol: deterministic_symbol_id("undefined"),
        def: None,
        type_id: None,
      });
    globals.entry("Error".to_string()).or_insert(SymbolBinding {
      symbol: deterministic_symbol_id("Error"),
      def: None,
      type_id: None,
    });
  }

  Arc::new(globals)
}

pub mod body_check {
  use std::cell::RefCell;
  use std::collections::{HashMap, HashSet};
  use std::fmt;
  use std::panic::panic_any;
  use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
  use std::sync::{Arc, OnceLock, RwLock};
  use std::time::Instant;

  use diagnostics::{Diagnostic, FileId, Span, TextRange};
  use hir_js::{
    Body as HirBody, BodyId as HirBodyId, BodyKind as HirBodyKind, DefId as HirDefId, NameInterner,
  };
  use hir_js::{PatId as HirPatId, PatKind as HirPatKind};
  use parse_js::ast::node::Node;
  use parse_js::ast::stx::TopLevel;
  use semantic_js::ts as sem_ts;
  use types_ts_interned::{
    IntrinsicKind, RelateCtx, TypeId as InternedTypeId, TypeParamDecl, TypeParamId, TypeStore,
  };

  use crate::check::caches::{CheckerCacheStats, CheckerCaches};
  use crate::check::hir_body::{
    check_body_with_env, check_body_with_expander, BindingTypeResolver,
  };
  use crate::codes;
  use crate::db::expander::{DbTypeExpander, TypeExpanderDb};
  use crate::files::FileRegistry;
  use crate::lib_support::{CacheMode, CacheOptions, JsxMode, ScriptTarget};
  use crate::profile::{QueryKind, QueryStatsCollector};
  use crate::program::check::relate_hooks;
  use crate::program::{NamespaceMemberIndex, ProgramTypeResolver};
  use crate::{BodyCheckResult, BodyId, DefId, ExportMap, Host, PatId, SymbolBinding, TypeId};

  #[derive(Clone)]
  pub struct ArcAst(Arc<Node<TopLevel>>);

  impl PartialEq for ArcAst {
    fn eq(&self, other: &Self) -> bool {
      Arc::ptr_eq(&self.0, &other.0)
    }
  }

  impl Eq for ArcAst {}

  impl fmt::Debug for ArcAst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      f.debug_tuple("ArcAst").finish()
    }
  }

  impl std::ops::Deref for ArcAst {
    type Target = Node<TopLevel>;

    fn deref(&self) -> &Self::Target {
      self.0.as_ref()
    }
  }

  #[derive(Clone)]
  pub struct ArcLowered(Arc<hir_js::LowerResult>);

  impl PartialEq for ArcLowered {
    fn eq(&self, other: &Self) -> bool {
      Arc::ptr_eq(&self.0, &other.0)
    }
  }

  impl Eq for ArcLowered {}

  impl fmt::Debug for ArcLowered {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      f.debug_tuple("ArcLowered").finish()
    }
  }

  impl std::ops::Deref for ArcLowered {
    type Target = hir_js::LowerResult;

    fn deref(&self) -> &Self::Target {
      self.0.as_ref()
    }
  }

  #[derive(Clone)]
  pub struct BodyCheckContext {
    pub store: Arc<TypeStore>,
    pub target: ScriptTarget,
    pub no_implicit_any: bool,
    pub use_define_for_class_fields: bool,
    pub interned_def_types: HashMap<DefId, InternedTypeId>,
    pub interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
    pub interned_type_param_decls: HashMap<DefId, Arc<[TypeParamDecl]>>,
    pub interned_intrinsics: HashMap<DefId, IntrinsicKind>,
    pub asts: HashMap<FileId, Arc<Node<TopLevel>>>,
    pub lowered: HashMap<FileId, Arc<hir_js::LowerResult>>,
    pub body_info: HashMap<BodyId, BodyInfo>,
    pub body_parents: HashMap<BodyId, BodyId>,
    pub global_bindings: HashMap<String, SymbolBinding>,
    pub file_bindings: HashMap<FileId, HashMap<String, SymbolBinding>>,
    pub def_spans: HashMap<(FileId, TextRange), DefId>,
    pub semantics: Option<Arc<sem_ts::TsProgramSemantics>>,
    pub def_kinds: Arc<HashMap<DefId, crate::DefKind>>,
    pub def_files: Arc<HashMap<DefId, FileId>>,
    pub def_id_spans: Arc<HashMap<DefId, TextRange>>,
    pub exports: Arc<HashMap<FileId, ExportMap>>,
    pub module_namespace_defs: Arc<HashMap<FileId, DefId>>,
    pub(crate) namespace_members: Arc<NamespaceMemberIndex>,
    pub qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
    pub(crate) file_registry: Arc<FileRegistry>,
    pub host: Arc<dyn Host>,
    pub checker_caches: CheckerCaches,
    pub cache_mode: CacheMode,
    pub cache_options: CacheOptions,
    pub jsx_mode: Option<JsxMode>,
    pub query_stats: QueryStatsCollector,
    pub cancelled: Arc<AtomicBool>,
  }

  #[derive(Clone, Copy, Debug, PartialEq, Eq)]
  pub struct BodyInfo {
    pub file: FileId,
    pub hir: Option<HirBodyId>,
    pub kind: HirBodyKind,
  }

  #[derive(Clone)]
  pub struct BodyCheckDb {
    context: Arc<BodyCheckContext>,
    memo: RefCell<HashMap<BodyId, Arc<BodyCheckResult>>>,
    ast_indexes: RefCell<HashMap<FileId, Arc<crate::check::hir_body::AstIndex>>>,
    cache_stats: RefCell<CheckerCacheStats>,
  }

  #[derive(Debug, Default)]
  pub struct ParallelTracker {
    active: AtomicUsize,
    max_active: AtomicUsize,
  }

  impl ParallelTracker {
    pub fn new() -> Self {
      Self::default()
    }

    pub fn max_active(&self) -> usize {
      self.max_active.load(Ordering::SeqCst)
    }
  }

  pub struct ParallelGuard {
    trackers: Vec<Arc<ParallelTracker>>,
  }

  impl Drop for ParallelGuard {
    fn drop(&mut self) {
      for tracker in &self.trackers {
        tracker.active.fetch_sub(1, Ordering::SeqCst);
      }
    }
  }

  impl ParallelGuard {
    fn new(trackers: Vec<Arc<ParallelTracker>>) -> Self {
      for tracker in trackers.iter() {
        let current = tracker.active.fetch_add(1, Ordering::SeqCst) + 1;
        tracker.max_active.fetch_max(current, Ordering::SeqCst);
      }
      ParallelGuard { trackers }
    }
  }

  static PARALLEL_TRACKER: OnceLock<RwLock<Vec<Arc<ParallelTracker>>>> = OnceLock::new();

  thread_local! {
    static LOCAL_TRACKER: RefCell<Option<Arc<ParallelTracker>>> = RefCell::new(None);
  }

  fn tracker_slot() -> &'static RwLock<Vec<Arc<ParallelTracker>>> {
    PARALLEL_TRACKER.get_or_init(|| RwLock::new(Vec::new()))
  }

  pub fn set_parallel_tracker(tracker: Option<Arc<ParallelTracker>>) {
    LOCAL_TRACKER.with(|local| {
      let mut local = local.borrow_mut();
      let mut global = tracker_slot().write().unwrap();

      if let Some(existing) = local.take() {
        global.retain(|registered| !Arc::ptr_eq(registered, &existing));
      }

      if let Some(tracker) = tracker {
        if !global
          .iter()
          .any(|registered| Arc::ptr_eq(registered, &tracker))
        {
          global.push(Arc::clone(&tracker));
        }
        *local = Some(tracker);
      }
    });
  }

  pub fn parallel_guard() -> Option<ParallelGuard> {
    let trackers: Vec<_> = tracker_slot().read().unwrap().iter().cloned().collect();
    (!trackers.is_empty()).then(|| ParallelGuard::new(trackers))
  }

  impl BodyCheckDb {
    pub fn new(context: BodyCheckContext) -> Self {
      Self::from_shared_context(Arc::new(context))
    }

    pub fn from_shared_context(context: Arc<BodyCheckContext>) -> Self {
      Self {
        context,
        memo: RefCell::new(HashMap::new()),
        ast_indexes: RefCell::new(HashMap::new()),
        cache_stats: RefCell::new(CheckerCacheStats::default()),
      }
    }

    pub fn from_shared_context_with_seed_results(
      context: Arc<BodyCheckContext>,
      seed_results: &[(BodyId, Arc<BodyCheckResult>)],
    ) -> Self {
      let memo = seed_results
        .iter()
        .map(|(body, res)| (*body, Arc::clone(res)))
        .collect();
      Self {
        context,
        memo: RefCell::new(memo),
        ast_indexes: RefCell::new(HashMap::new()),
        cache_stats: RefCell::new(CheckerCacheStats::default()),
      }
    }

    pub(crate) fn into_cache_stats(self) -> CheckerCacheStats {
      self.cache_stats.into_inner()
    }
  }

  impl TypeExpanderDb for BodyCheckContext {
    fn type_store(&self) -> Arc<TypeStore> {
      Arc::clone(&self.store)
    }

    fn decl_type(&self, def: types_ts_interned::DefId) -> Option<InternedTypeId> {
      self
        .interned_def_types
        .get(&crate::api::DefId(def.0))
        .copied()
    }

    fn type_params(&self, def: types_ts_interned::DefId) -> Arc<[TypeParamId]> {
      self
        .interned_type_params
        .get(&crate::api::DefId(def.0))
        .cloned()
        .map(Arc::from)
        .unwrap_or_else(|| Arc::from([]))
    }

    fn type_param_decls(&self, def: types_ts_interned::DefId) -> Option<Arc<[TypeParamDecl]>> {
      self
        .interned_type_param_decls
        .get(&crate::api::DefId(def.0))
        .cloned()
    }

    fn type_of_def(&self, def: types_ts_interned::DefId) -> Option<InternedTypeId> {
      self
        .interned_def_types
        .get(&crate::api::DefId(def.0))
        .copied()
    }

    fn intrinsic_kind(&self, def: types_ts_interned::DefId) -> Option<IntrinsicKind> {
      self
        .interned_intrinsics
        .get(&crate::api::DefId(def.0))
        .copied()
    }
  }

  impl BodyCheckDb {
    fn bc_parse(&self, file: FileId) -> Option<ArcAst> {
      self.context.asts.get(&file).cloned().map(ArcAst)
    }

    fn bc_lower_hir(&self, file: FileId) -> Option<ArcLowered> {
      let _ = self.bc_parse(file)?;
      self.context.lowered.get(&file).cloned().map(ArcLowered)
    }

    fn bc_body_info(&self, body: BodyId) -> Option<BodyInfo> {
      self.context.body_info.get(&body).copied()
    }
  }

  fn missing_body(body: BodyId) -> BodyCheckResult {
    BodyCheckResult {
      body,
      expr_types: Vec::new(),
      expr_spans: Vec::new(),
      pat_types: Vec::new(),
      pat_spans: Vec::new(),
      diagnostics: vec![codes::MISSING_BODY.error(
        "missing body",
        Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
      )],
      return_types: Vec::new(),
    }
  }

  fn missing_ast(body: BodyId, file: FileId) -> BodyCheckResult {
    BodyCheckResult {
      body,
      expr_types: Vec::new(),
      expr_spans: Vec::new(),
      pat_types: Vec::new(),
      pat_spans: Vec::new(),
      diagnostics: vec![codes::MISSING_BODY.error(
        "missing parsed AST for body",
        Span::new(file, TextRange::new(0, 0)),
      )],
      return_types: Vec::new(),
    }
  }

  fn empty_result(body: BodyId) -> BodyCheckResult {
    BodyCheckResult {
      body,
      expr_types: Vec::new(),
      expr_spans: Vec::new(),
      pat_types: Vec::new(),
      pat_spans: Vec::new(),
      diagnostics: Vec::new(),
      return_types: Vec::new(),
    }
  }

  impl BodyCheckDb {
    pub fn check_body(&self, body_id: BodyId) -> Arc<BodyCheckResult> {
      if let Some(cached) = self.memo.borrow().get(&body_id).cloned() {
        return cached;
      }
      let res = self.compute_body(body_id);
      self.memo.borrow_mut().insert(body_id, Arc::clone(&res));
      res
    }

    fn ast_index(&self, file: FileId, ast: &ArcAst) -> Arc<crate::check::hir_body::AstIndex> {
      let cached = self.ast_indexes.borrow().get(&file).cloned();
      if let Some(index) = cached {
        return index;
      }
      let index = Arc::new(crate::check::hir_body::AstIndex::new(
        Arc::clone(&ast.0),
        file,
        Some(&self.context.cancelled),
      ));
      self
        .ast_indexes
        .borrow_mut()
        .insert(file, Arc::clone(&index));
      index
    }

    fn compute_body(&self, body_id: BodyId) -> Arc<BodyCheckResult> {
      if self.context.cancelled.load(Ordering::Relaxed) {
        panic_any(crate::FatalError::Cancelled);
      }
      let started = Instant::now();
      let ctx = &self.context;
      let Some(meta) = self.bc_body_info(body_id) else {
        return Arc::new(missing_body(body_id));
      };
      let Some(lowered) = self.bc_lower_hir(meta.file) else {
        return Arc::new(empty_result(body_id));
      };
      let Some(ast) = self.bc_parse(meta.file) else {
        return Arc::new(missing_ast(body_id, meta.file));
      };

      let mut _synthetic = None;
      let body = if let Some(hir_id) = meta.hir {
        lowered.body(hir_id)
      } else if matches!(meta.kind, HirBodyKind::TopLevel) {
        _synthetic = Some(HirBody {
          owner: HirDefId(u32::MAX),
          span: TextRange::new(0, 0),
          kind: HirBodyKind::TopLevel,
          exprs: Vec::new(),
          stmts: Vec::new(),
          pats: Vec::new(),
          root_stmts: Vec::new(),
          function: None,
          class: None,
          expr_types: None,
        });
        _synthetic.as_ref()
      } else {
        None
      };
      let Some(body) = body else {
        return Arc::new(empty_result(body_id));
      };
      let _parallel_guard = parallel_guard();

      let prim = ctx.store.primitive_ids();
      let map_def_ty = |def: DefId| {
        ctx
          .interned_def_types
          .get(&def)
          .copied()
          .unwrap_or(prim.unknown)
      };

      let mut bindings: HashMap<String, TypeId> = HashMap::new();
      let mut binding_defs: HashMap<String, DefId> = HashMap::new();

      seed_bindings(
        &mut bindings,
        &mut binding_defs,
        &ctx.global_bindings,
        map_def_ty,
        prim.unknown,
      );
      if let Some(file_bindings) = ctx.file_bindings.get(&meta.file) {
        seed_bindings(
          &mut bindings,
          &mut binding_defs,
          file_bindings,
          map_def_ty,
          prim.unknown,
        );
      }

      collect_parent_bindings(
        self,
        body_id,
        &mut bindings,
        &mut binding_defs,
        prim.unknown,
      );

      let caches = ctx.checker_caches.for_body();
      let expander = DbTypeExpander::new(ctx.as_ref(), caches.eval.clone());
      let contextual_fn_ty = if matches!(meta.kind, HirBodyKind::Function) {
        function_expr_span(self, body_id)
          .and_then(|span| contextual_callable_for_body(self, body_id, span))
      } else {
        None
      };
      let resolver = if let Some(semantics) = ctx.semantics.as_ref() {
        Some(Arc::new(ProgramTypeResolver::new(
          Arc::clone(&ctx.host),
          Arc::clone(semantics),
          Arc::clone(&ctx.def_kinds),
          Arc::clone(&ctx.def_files),
          Arc::clone(&ctx.def_id_spans),
          Arc::clone(&ctx.file_registry),
          meta.file,
          binding_defs,
          Arc::clone(&ctx.exports),
          Arc::clone(&ctx.module_namespace_defs),
          Arc::clone(&ctx.namespace_members),
          Arc::clone(&ctx.qualified_def_members),
        )) as Arc<_>)
      } else if binding_defs.is_empty() {
        None
      } else {
        Some(Arc::new(BindingTypeResolver::new(binding_defs)) as Arc<_>)
      };
      let ast_index = self.ast_index(meta.file, &ast);
      let mut result = check_body_with_expander(
        body_id,
        body,
        &lowered.names,
        meta.file,
        ast_index.as_ref(),
        Arc::clone(&ctx.store),
        ctx.target,
        ctx.use_define_for_class_fields,
        &caches,
        &bindings,
        resolver,
        Some(&expander),
        Some(&ctx.interned_type_param_decls),
        contextual_fn_ty,
        ctx.no_implicit_any,
        ctx.jsx_mode,
        Some(&ctx.cancelled),
      );

      if !body.exprs.is_empty()
        && matches!(meta.kind, HirBodyKind::Function | HirBodyKind::TopLevel)
      {
        if ctx.cancelled.load(Ordering::Relaxed) {
          panic_any(crate::FatalError::Cancelled);
        }
        let mut initial_env: HashMap<_, _> = HashMap::new();
        fn record_param_pats(
          body: &HirBody,
          pat_id: HirPatId,
          pat_types: &[TypeId],
          unknown: TypeId,
          initial_env: &mut HashMap<hir_js::NameId, TypeId>,
        ) {
          let Some(pat) = body.pats.get(pat_id.0 as usize) else {
            return;
          };
          match &pat.kind {
            HirPatKind::Ident(name_id) => {
              if let Some(ty) = pat_types.get(pat_id.0 as usize).copied() {
                if ty != unknown {
                  initial_env.insert(*name_id, ty);
                }
              }
            }
            HirPatKind::Array(arr) => {
              for elem in arr.elements.iter().flatten() {
                record_param_pats(body, elem.pat, pat_types, unknown, initial_env);
              }
              if let Some(rest) = arr.rest {
                record_param_pats(body, rest, pat_types, unknown, initial_env);
              }
            }
            HirPatKind::Object(obj) => {
              for prop in obj.props.iter() {
                record_param_pats(body, prop.value, pat_types, unknown, initial_env);
              }
              if let Some(rest) = obj.rest {
                record_param_pats(body, rest, pat_types, unknown, initial_env);
              }
            }
            HirPatKind::Rest(inner) => {
              record_param_pats(body, **inner, pat_types, unknown, initial_env);
            }
            HirPatKind::Assign { target, .. } => {
              record_param_pats(body, *target, pat_types, unknown, initial_env);
            }
            HirPatKind::AssignTarget(_) => {}
          }
        }

        if let Some(function) = body.function.as_ref() {
          for param in function.params.iter() {
            record_param_pats(
              body,
              param.pat,
              &result.pat_types,
              prim.unknown,
              &mut initial_env,
            );
          }
        }
        for (idx, expr) in body.exprs.iter().enumerate() {
          if let hir_js::ExprKind::Ident(name_id) = expr.kind {
            if initial_env.contains_key(&name_id) {
              continue;
            }
            if let Some(name) = lowered.names.resolve(name_id) {
              let binding_ty = bindings.get(name).copied();
              let candidate = match binding_ty {
                Some(ty) if ty != prim.unknown => Some(ty),
                _ => result
                  .expr_types
                  .get(idx)
                  .copied()
                  .filter(|t| *t != prim.unknown),
              };
              if let Some(ty) = candidate {
                initial_env.insert(name_id, ty);
              }
            }
          }
        }
        let mut flow_hooks = relate_hooks();
        flow_hooks.expander = Some(&expander);
        let flow_relate = RelateCtx::with_hooks_and_cache(
          Arc::clone(&ctx.store),
          ctx.store.options(),
          flow_hooks,
          caches.relation.clone(),
        );
        let flow_result = check_body_with_env(
          body_id,
          body,
          &lowered.names,
          meta.file,
          "",
          Arc::clone(&ctx.store),
          &initial_env,
          flow_relate,
          Some(&expander),
        );
        let mut relate_hooks = relate_hooks();
        relate_hooks.expander = Some(&expander);
        let relate = RelateCtx::with_hooks_and_cache(
          Arc::clone(&ctx.store),
          ctx.store.options(),
          relate_hooks,
          caches.relation.clone(),
        );
        if flow_result.expr_types.len() == result.expr_types.len() {
          for (idx, ty) in flow_result.expr_types.iter().enumerate() {
            if *ty != prim.unknown {
              let existing = result.expr_types[idx];
              let narrower =
                relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
              let flow_literal_on_primitive = matches!(
                (ctx.store.type_kind(existing), ctx.store.type_kind(*ty)),
                (
                  types_ts_interned::TypeKind::Number,
                  types_ts_interned::TypeKind::NumberLiteral(_)
                ) | (
                  types_ts_interned::TypeKind::String,
                  types_ts_interned::TypeKind::StringLiteral(_),
                ) | (
                  types_ts_interned::TypeKind::Boolean,
                  types_ts_interned::TypeKind::BooleanLiteral(_),
                ) | (
                  types_ts_interned::TypeKind::BigInt,
                  types_ts_interned::TypeKind::BigIntLiteral(_),
                )
              );
              if existing == prim.unknown || (narrower && !flow_literal_on_primitive) {
                result.expr_types[idx] = *ty;
              }
            }
          }
        }
        if flow_result.pat_types.len() == result.pat_types.len() {
          for (idx, ty) in flow_result.pat_types.iter().enumerate() {
            if *ty != prim.unknown {
              let existing = result.pat_types[idx];
              let narrower =
                relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
              let flow_literal_on_primitive = matches!(
                (ctx.store.type_kind(existing), ctx.store.type_kind(*ty)),
                (
                  types_ts_interned::TypeKind::Number,
                  types_ts_interned::TypeKind::NumberLiteral(_)
                ) | (
                  types_ts_interned::TypeKind::String,
                  types_ts_interned::TypeKind::StringLiteral(_),
                ) | (
                  types_ts_interned::TypeKind::Boolean,
                  types_ts_interned::TypeKind::BooleanLiteral(_),
                ) | (
                  types_ts_interned::TypeKind::BigInt,
                  types_ts_interned::TypeKind::BigIntLiteral(_),
                )
              );
              if existing == prim.unknown || (narrower && !flow_literal_on_primitive) {
                result.pat_types[idx] = *ty;
              }
            }
          }
        }
        let flow_return_types: Vec<_> = flow_result
          .return_types
          .into_iter()
          .map(|ty| crate::check::widen::widen_literal(ctx.store.as_ref(), ty))
          .collect();
        if result.return_types.is_empty() && !flow_return_types.is_empty() {
          result.return_types = flow_return_types;
        } else if flow_return_types.len() == result.return_types.len() {
          for (idx, ty) in flow_return_types.iter().enumerate() {
            if *ty != prim.unknown {
              let existing = result.return_types[idx];
              let narrower =
                relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
              if existing == prim.unknown || narrower {
                result.return_types[idx] = *ty;
              }
            }
          }
        }
        if !result.return_types.is_empty() {
          result.return_types = result
            .return_types
            .iter()
            .map(|ty| crate::check::widen::widen_literal(ctx.store.as_ref(), *ty))
            .collect();
        }
        let mut flow_diagnostics = flow_result.diagnostics;
        if !flow_diagnostics.is_empty() {
          let mut seen: HashSet<(String, FileId, TextRange, String)> = HashSet::new();
          let diag_key = |diag: &Diagnostic| -> (String, FileId, TextRange, String) {
            (
              diag.code.as_str().to_string(),
              diag.primary.file,
              diag.primary.range,
              diag.message.clone(),
            )
          };
          for diag in result.diagnostics.iter() {
            seen.insert(diag_key(diag));
          }
          flow_diagnostics.sort_by(|a, b| {
            a.primary
              .file
              .cmp(&b.primary.file)
              .then(a.primary.range.start.cmp(&b.primary.range.start))
              .then(a.primary.range.end.cmp(&b.primary.range.end))
              .then(a.code.cmp(&b.code))
              .then(a.message.cmp(&b.message))
          });
          for diag in flow_diagnostics.into_iter() {
            if seen.insert(diag_key(&diag)) {
              result.diagnostics.push(diag);
            }
          }
        }
      }

      let res = Arc::new(result);

      if matches!(ctx.cache_mode, CacheMode::PerBody) {
        let mut stats = caches.stats();
        if stats.relation.evictions == 0 {
          let max = ctx.cache_options.max_relation_cache_entries as u64;
          if max > 0 && stats.relation.insertions > max {
            stats.relation.evictions = stats.relation.insertions - max;
          } else {
            stats.relation.evictions = 1;
          }
        }
        self.cache_stats.borrow_mut().merge(&stats);
        ctx
          .query_stats
          .record_cache(crate::profile::CacheKind::Relation, &stats.relation);
        ctx
          .query_stats
          .record_cache(crate::profile::CacheKind::Eval, &stats.eval);
        ctx.query_stats.record_cache(
          crate::profile::CacheKind::RefExpansion,
          &stats.ref_expansion,
        );
        ctx.query_stats.record_cache(
          crate::profile::CacheKind::Instantiation,
          &stats.instantiation,
        );
      }
      ctx
        .query_stats
        .record(QueryKind::CheckBody, false, started.elapsed());

      res
    }
  }

  pub fn check_body(db: &BodyCheckDb, body_id: BodyId) -> Arc<BodyCheckResult> {
    db.check_body(body_id)
  }

  fn record_pat(
    ctx: &BodyCheckContext,
    pat_id: HirPatId,
    body: &HirBody,
    names: &NameInterner,
    result: &BodyCheckResult,
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
    file: FileId,
    unknown: TypeId,
    seen: &mut HashSet<String>,
  ) {
    let Some(pat) = body.pats.get(pat_id.0 as usize) else {
      return;
    };
    let ty = result.pat_type(PatId(pat_id.0)).unwrap_or(unknown);
    match &pat.kind {
      HirPatKind::Ident(name_id) => {
        if let Some(name) = names.resolve(*name_id) {
          let name = name.to_string();
          if !seen.insert(name.clone()) {
            return;
          }
          bindings.insert(name.clone(), ty);
          if let Some(def_id) = ctx.def_spans.get(&(file, pat.span)).copied() {
            binding_defs.insert(name, def_id);
          }
        }
      }
      HirPatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          record_pat(
            ctx,
            elem.pat,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            unknown,
            seen,
          );
        }
        if let Some(rest) = arr.rest {
          record_pat(
            ctx,
            rest,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            unknown,
            seen,
          );
        }
      }
      HirPatKind::Object(obj) => {
        for prop in obj.props.iter() {
          record_pat(
            ctx,
            prop.value,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            unknown,
            seen,
          );
        }
        if let Some(rest) = obj.rest {
          record_pat(
            ctx,
            rest,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            unknown,
            seen,
          );
        }
      }
      HirPatKind::Rest(inner) => {
        record_pat(
          ctx,
          **inner,
          body,
          names,
          result,
          bindings,
          binding_defs,
          file,
          unknown,
          seen,
        );
      }
      HirPatKind::Assign { target, .. } => {
        record_pat(
          ctx,
          *target,
          body,
          names,
          result,
          bindings,
          binding_defs,
          file,
          unknown,
          seen,
        );
      }
      HirPatKind::AssignTarget(_) => {}
    }
  }

  fn seed_bindings(
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
    source: &HashMap<String, SymbolBinding>,
    map_def_ty: impl Fn(DefId) -> TypeId,
    unknown: TypeId,
  ) {
    for (name, binding) in source.iter() {
      let ty = if let Some(def) = binding.def {
        map_def_ty(def)
      } else if let Some(ty) = binding.type_id {
        ty
      } else {
        unknown
      };
      bindings.insert(name.clone(), ty);
      if let Some(def) = binding.def {
        binding_defs.insert(name.clone(), def);
      }
    }
  }

  fn collect_parent_bindings(
    db: &BodyCheckDb,
    body_id: BodyId,
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
    unknown: TypeId,
  ) {
    let ctx = &db.context;
    let mut visited = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut current = ctx.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let parent_result = db.check_body(parent);
      let Some(meta) = db.bc_body_info(parent) else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      let Some(hir_id) = meta.hir else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = db.bc_lower_hir(meta.file) else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      let Some(body) = lowered.body(hir_id) else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      for idx in 0..body.pats.len() {
        record_pat(
          ctx,
          HirPatId(idx as u32),
          body,
          &lowered.names,
          &parent_result,
          bindings,
          binding_defs,
          meta.file,
          unknown,
          &mut seen_names,
        );
      }
      current = ctx.body_parents.get(&parent).copied();
    }
  }

  fn function_expr_span(db: &BodyCheckDb, body_id: BodyId) -> Option<TextRange> {
    let ctx = &db.context;
    let mut visited = HashSet::new();
    let mut current = ctx.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let Some(meta) = db.bc_body_info(parent) else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      let Some(hir_body_id) = meta.hir else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = db.bc_lower_hir(meta.file) else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      let Some(parent_body) = lowered.body(hir_body_id) else {
        current = ctx.body_parents.get(&parent).copied();
        continue;
      };
      for expr in parent_body.exprs.iter() {
        if let hir_js::ExprKind::FunctionExpr { body, .. } = expr.kind {
          if body == body_id {
            return Some(expr.span);
          }
        }
      }
      current = ctx.body_parents.get(&parent).copied();
    }
    None
  }

  fn contextual_callable_for_body(
    db: &BodyCheckDb,
    body_id: BodyId,
    func_span: TextRange,
  ) -> Option<TypeId> {
    let store = &db.context.store;
    let mut visited = HashSet::new();
    let mut current = db.context.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let parent_result = db.check_body(parent);
      for (idx, span) in parent_result.expr_spans.iter().enumerate() {
        if *span != func_span {
          continue;
        }
        if let Some(ty) = parent_result.expr_types.get(idx).copied() {
          if store.contains_type_id(ty)
            && matches!(
              store.type_kind(ty),
              types_ts_interned::TypeKind::Callable { .. }
            )
          {
            return Some(ty);
          }
        }
      }
      current = db.context.body_parents.get(&parent).copied();
    }
    None
  }
}
impl Eq for LowerResultWithDiagnostics {}

pub fn parse_query_count() -> usize {
  parse_metrics::parse_call_count()
}

pub fn reset_parse_query_count() {
  parse_metrics::reset_parse_call_count();
}

#[salsa::tracked]
fn parse_for(db: &dyn Db, file: FileInput) -> parser::ParseResult {
  panic_if_cancelled(db);
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::Parse, false));
  parse_metrics::record_parse_call();
  let kind = file.kind(db);
  let source = file.text(db);
  let file_id = file.file_id(db);
  let dialect = match kind {
    FileKind::Js => Dialect::Js,
    FileKind::Ts => Dialect::Ts,
    FileKind::Tsx => Dialect::Tsx,
    FileKind::Jsx => Dialect::Jsx,
    FileKind::Dts => Dialect::Dts,
  };
  let cancel = cancelled(db);
  match parse_with_options_cancellable(
    &source,
    ParseOptions {
      dialect,
      source_type: SourceType::Module,
    },
    Arc::clone(&cancel),
  ) {
    Ok(ast) => parser::ParseResult::ok(ast),
    Err(err) => {
      if err.typ == SyntaxErrorType::Cancelled {
        panic_any(crate::FatalError::Cancelled);
      }
      parser::ParseResult::error(err.to_diagnostic(file_id))
    }
  }
}

#[salsa::tracked]
fn lower_hir_for(db: &dyn Db, file: FileInput) -> LowerResultWithDiagnostics {
  panic_if_cancelled(db);
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::LowerHir, false));
  lower_metrics::record_lower_call();
  let parsed = parse_for(db, file);
  panic_if_cancelled(db);
  let file_kind = file.kind(db);
  let mut diagnostics = parsed.diagnostics.clone();
  let cancelled_flag = cancelled(db);
  let lowered = parsed.ast.as_ref().map(|ast| {
    panic_if_cancelled(db);
    let (lowered, mut lower_diags) = lower_file_with_diagnostics_with_cancellation(
      file.file_id(db),
      map_hir_file_kind(file_kind),
      ast,
      Some(Arc::clone(&cancelled_flag)),
    );
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
  let parsed = parse_for(db, file);
  match (parsed.ast.as_ref(), lowered.lowered.as_ref()) {
    (Some(ast), Some(lowered)) => sem_ts::from_hir_js::lower_to_ts_hir(ast, lowered),
    _ => empty_sem_hir(file.file_id(db), lowered.file_kind),
  }
}

#[salsa::tracked]
fn symbol_index_for(db: &dyn Db, file: FileInput) -> SymbolIndex {
  panic_if_cancelled(db);
  let file_id = file.file_id(db);
  let kind = file.kind(db);
  let parsed = parse_for(db, file);
  if parsed.ast.is_none() {
    return SymbolIndex::empty();
  }
  let source = file_text_for(db, file);
  let dialect = match kind {
    FileKind::Js => Dialect::Js,
    FileKind::Ts => Dialect::Ts,
    FileKind::Tsx => Dialect::Tsx,
    FileKind::Jsx => Dialect::Jsx,
    FileKind::Dts => Dialect::Dts,
  };
  let cancel = cancelled(db);
  let ast = match parse_with_options_cancellable(
    &source,
    ParseOptions {
      dialect,
      source_type: SourceType::Module,
    },
    Arc::clone(&cancel),
  ) {
    Ok(ast) => ast,
    Err(err) => {
      if err.typ == SyntaxErrorType::Cancelled {
        panic_any(crate::FatalError::Cancelled);
      }
      return SymbolIndex::empty();
    }
  };
  let semantics = ts_semantics_for(db);
  symbols::symbol_index_for_file(file_id, kind, ast, Some(semantics.semantics.as_ref()))
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
    type_imports: Vec::new(),
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
  panic_if_cancelled(db);
  let mut visited = AHashSet::new();
  let root_ids: Vec<FileId> = db
    .roots_input()
    .roots(db)
    .iter()
    .filter_map(|key| file_id_from_key(db, key))
    .collect();
  let mut queue: VecDeque<FileId> = root_ids.iter().copied().collect();
  visited.reserve(queue.len());
  // Always seed bundled/host libs by `FileId` to avoid losing them when a host
  // file shares the same `FileKey` as a bundled lib (two IDs, one key).
  let mut lib_files = db.lib_files();
  lib_files.sort_by_key(|id| id.0);
  queue.extend(lib_files);
  let options = compiler_options(db);
  if !options.types.is_empty() && !root_ids.is_empty() {
    let mut type_names: Vec<&str> = options.types.iter().map(|s| s.as_str()).collect();
    type_names.sort_unstable();
    type_names.dedup();
    for name in type_names {
      panic_if_cancelled(db);
      for root in &root_ids {
        if let Some(target) = module_resolve_ref(db, *root, name) {
          queue.push_back(target);
        }
      }
    }
  }
  while let Some(file) = queue.pop_front() {
    panic_if_cancelled(db);
    if !visited.insert(file) {
      continue;
    }
    queue.extend(
      module_deps_for(db, db.file_input(file).expect("file seeded for deps"))
        .iter()
        .copied(),
    );
  }
  let mut files: Vec<FileId> = visited.into_iter().collect();
  files.sort_unstable_by_key(|id| id.0);
  Arc::new(files)
}

#[salsa::tracked]
fn ts_semantics_for(db: &dyn Db) -> Arc<TsSemantics> {
  panic_if_cancelled(db);
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::Bind, false));
  let files = all_files_for(db);
  let mut diagnostics = Vec::new();
  let mut sem_hirs: AHashMap<sem_ts::FileId, Arc<sem_ts::HirFile>> = AHashMap::new();
  sem_hirs.reserve(files.len());
  for file in files.iter() {
    panic_if_cancelled(db);
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

  let roots: Vec<_> = files.iter().map(|id| sem_ts::FileId(id.0)).collect();
  let resolver = DbResolver { db };
  let cancelled_flag = cancelled(db);
  let (semantics, mut bind_diags) = sem_ts::bind_ts_program_with_cancellation(
    &roots,
    &resolver,
    |file| {
      sem_hirs.get(&file).cloned().unwrap_or_else(|| {
        Arc::new(empty_sem_hir(
          FileId(file.0),
          db.file_input(FileId(file.0))
            .map(|input| input.kind(db))
            .unwrap_or(FileKind::Ts),
        ))
      })
    },
    Some(cancelled_flag.as_ref()),
  );
  panic_if_cancelled(db);
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
    module_resolve_ref(self.db, FileId(from.0), specifier).map(|id| sem_ts::FileId(id.0))
  }
}

fn collect_module_specifiers(lowered: &hir_js::LowerResult, specs: &mut Vec<Arc<str>>) {
  for import in lowered.hir.imports.iter() {
    match &import.kind {
      hir_js::ImportKind::Es(es) => {
        specs.push(Arc::<str>::from(es.specifier.value.as_str()));
      }
      hir_js::ImportKind::ImportEquals(eq) => {
        if let hir_js::ImportEqualsTarget::Module(module) = &eq.target {
          specs.push(Arc::<str>::from(module.value.as_str()));
        }
      }
    }
  }
  for export in lowered.hir.exports.iter() {
    match &export.kind {
      ExportKind::Named(named) => {
        if let Some(source) = named.source.as_ref() {
          specs.push(Arc::<str>::from(source.value.as_str()));
        }
      }
      ExportKind::ExportAll(all) => {
        specs.push(Arc::<str>::from(all.source.value.as_str()));
      }
      _ => {}
    }
  }
  for arenas in lowered.types.values() {
    for ty in arenas.type_exprs.iter() {
      match &ty.kind {
        hir_js::TypeExprKind::TypeRef(type_ref) => {
          if let hir_js::TypeName::Import(import) = &type_ref.name {
            if let Some(module) = &import.module {
              specs.push(Arc::<str>::from(module.as_str()));
            }
          }
        }
        hir_js::TypeExprKind::TypeQuery(name) => {
          if let hir_js::TypeName::Import(import) = name {
            if let Some(module) = &import.module {
              specs.push(Arc::<str>::from(module.as_str()));
            }
          }
        }
        hir_js::TypeExprKind::Import(import) => {
          specs.push(Arc::<str>::from(import.module.as_str()));
        }
        _ => {}
      }
    }
  }
}

fn collect_type_only_module_specifier_values_from_ast(
  ast: &parse_js::ast::node::Node<parse_js::ast::stx::TopLevel>,
  specs: &mut Vec<Arc<str>>,
) {
  use derive_visitor::Drive;
  use derive_visitor::Visitor;
  use parse_js::ast::expr::Expr;
  use parse_js::ast::node::Node;
  use parse_js::ast::type_expr::{TypeEntityName, TypeExpr};

  type TypeExprNode = Node<TypeExpr>;

  fn collect_from_entity_name(name: &TypeEntityName, specs: &mut Vec<Arc<str>>) {
    match name {
      TypeEntityName::Qualified(qualified) => collect_from_entity_name(&qualified.left, specs),
      TypeEntityName::Import(import) => {
        if let Expr::LitStr(spec) = import.stx.module.stx.as_ref() {
          specs.push(Arc::<str>::from(spec.stx.value.as_str()));
        }
      }
      _ => {}
    }
  }

  #[derive(Visitor)]
  #[visitor(TypeExprNode(enter))]
  struct Collector<'a> {
    specs: &'a mut Vec<Arc<str>>,
  }

  impl<'a> Collector<'a> {
    fn enter_type_expr_node(&mut self, node: &TypeExprNode) {
      match node.stx.as_ref() {
        TypeExpr::ImportType(import) => {
          self
            .specs
            .push(Arc::<str>::from(import.stx.module_specifier.as_str()));
        }
        TypeExpr::TypeQuery(query) => {
          collect_from_entity_name(&query.stx.expr_name, self.specs);
        }
        _ => {}
      }
    }
  }

  let mut collector = Collector { specs };
  ast.drive(&mut collector);
}

fn ast_has_module_syntax(ast: &parse_js::ast::node::Node<parse_js::ast::stx::TopLevel>) -> bool {
  use parse_js::ast::node::Node;
  use parse_js::ast::stmt::Stmt;
  use parse_js::ast::ts_stmt::ImportEqualsRhs;

  fn walk(stmts: &[Node<Stmt>]) -> bool {
    for stmt in stmts.iter() {
      match stmt.stx.as_ref() {
        Stmt::Import(_)
        | Stmt::ExportList(_)
        | Stmt::ExportDefaultExpr(_)
        | Stmt::ExportAssignmentDecl(_)
        | Stmt::ExportAsNamespaceDecl(_)
        | Stmt::ImportTypeDecl(_)
        | Stmt::ExportTypeDecl(_) => return true,
        Stmt::ImportEqualsDecl(import_equals) => match import_equals.stx.rhs {
          ImportEqualsRhs::Require { .. } => return true,
          ImportEqualsRhs::EntityName { .. } => {
            if import_equals.stx.export {
              return true;
            }
          }
        },
        Stmt::VarDecl(var) => {
          if var.stx.export {
            return true;
          }
        }
        Stmt::FunctionDecl(func) => {
          if func.stx.export {
            return true;
          }
        }
        Stmt::ClassDecl(class) => {
          if class.stx.export {
            return true;
          }
        }
        Stmt::InterfaceDecl(interface) => {
          if interface.stx.export {
            return true;
          }
        }
        Stmt::TypeAliasDecl(alias) => {
          if alias.stx.export {
            return true;
          }
        }
        Stmt::EnumDecl(en) => {
          if en.stx.export {
            return true;
          }
        }
        Stmt::NamespaceDecl(ns) => {
          if ns.stx.export {
            return true;
          }
        }
        Stmt::ModuleDecl(module) => {
          if module.stx.export {
            return true;
          }
        }
        Stmt::AmbientVarDecl(av) => {
          if av.stx.export {
            return true;
          }
        }
        Stmt::AmbientFunctionDecl(af) => {
          if af.stx.export {
            return true;
          }
        }
        Stmt::AmbientClassDecl(ac) => {
          if ac.stx.export {
            return true;
          }
        }
        Stmt::GlobalDecl(global) => {
          if walk(&global.stx.body) {
            return true;
          }
        }
        _ => {}
      }
    }
    false
  }

  walk(&ast.stx.body)
}

fn collect_module_augmentation_specifier_values_from_ast(
  ast: &parse_js::ast::node::Node<parse_js::ast::stx::TopLevel>,
  specs: &mut Vec<Arc<str>>,
) {
  if !ast_has_module_syntax(ast) {
    return;
  }

  use parse_js::ast::node::Node;
  use parse_js::ast::stmt::Stmt;
  use parse_js::ast::ts_stmt::ModuleName;

  fn walk(stmts: &[Node<Stmt>], specs: &mut Vec<Arc<str>>) {
    for stmt in stmts {
      match stmt.stx.as_ref() {
        Stmt::ModuleDecl(module) => {
          if let ModuleName::String(spec) = &module.stx.name {
            specs.push(Arc::<str>::from(spec.as_str()));
          }
        }
        Stmt::GlobalDecl(global) => walk(&global.stx.body, specs),
        _ => {}
      }
    }
  }

  walk(&ast.stx.body, specs);
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

pub fn unresolved_module_diagnostics(db: &dyn Db, file: FileId) -> Arc<[Diagnostic]> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before querying module deps");
  unresolved_module_diagnostics_for(db, handle)
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

pub fn symbol_occurrences(db: &dyn Db, file: FileId) -> Arc<[SymbolOccurrence]> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before computing symbol occurrences");
  symbol_index_for(db, handle).occurrences
}

pub fn local_symbol_info(db: &dyn Db, file: FileId) -> Arc<BTreeMap<SymbolId, LocalSymbolInfo>> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before computing symbol info");
  symbol_index_for(db, handle).locals
}

#[salsa::tracked]
fn file_span_index_for(db: &dyn Db, file: FileInput) -> Arc<FileSpanIndex> {
  let lowered = lower_hir_for(db, file);
  let Some(lowered) = lowered.lowered.as_ref() else {
    return Arc::new(FileSpanIndex::default());
  };

  Arc::new(FileSpanIndex::from_lowered(lowered))
}

/// Cached span index for a file, built from lowered HIR expression spans.
pub fn file_span_index(db: &dyn Db, file: FileId) -> Arc<FileSpanIndex> {
  let handle = db
    .file_input(file)
    .expect("file must be seeded before building span index");
  file_span_index_for(db, handle)
}

/// Innermost expression covering an offset within a file.
pub fn expr_at(db: &dyn Db, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
  let index = file_span_index(db, file);
  let body = index.body_at(offset)?;

  if let Some(result) = db.body_result(body) {
    if let Some((expr, _)) = expr_at_from_spans(result.expr_spans(), offset) {
      return Some((body, expr));
    }
  }

  index
    .expr_at_in_body(body, offset)
    .map(|(expr, _span)| (body, expr))
}

/// Span for a specific expression within a body.
pub fn span_of_expr(db: &dyn Db, body: BodyId, expr: ExprId) -> Option<Span> {
  let file = body_file(db, body)?;
  if let Some(result) = db.body_result(body) {
    if let Some(range) = result.expr_span(expr) {
      return Some(Span::new(file, range));
    }
  }
  file_span_index(db, file)
    .span_of_expr(body, expr)
    .map(|range| Span::new(file, range))
}

/// Span for a definition using its lowered HIR span, if available.
pub fn span_of_def(db: &dyn Db, def: DefId) -> Option<Span> {
  let file = def_file(db, def)?;
  let lowered = lower_hir(db, file);
  let lowered = lowered.lowered.as_ref()?;
  lowered.def(def).map(|data| Span::new(file, data.span))
}

/// Type of the innermost expression at the given offset, if available.
///
/// This uses cached [`BodyCheckResult`]s stored in the database by
/// [`Program::check_body`](crate::Program::check_body). When no cached result is
/// available the query returns `None` to avoid triggering type checking from
/// within salsa.
pub fn type_at(db: &dyn Db, file: FileId, offset: u32) -> Option<TypeId> {
  let (body, expr) = expr_at(db, file, offset)?;
  let result = db.body_result(body)?;
  if let Some((_, ty)) = result.expr_at(offset) {
    return Some(ty);
  }
  result.expr_type(expr)
}

/// Host-provided module resolution result.
pub fn module_resolve(db: &dyn Db, from: FileId, specifier: Arc<str>) -> Option<FileId> {
  module_resolve_ref(db, from, specifier.as_ref())
}

pub fn module_resolve_ref(db: &dyn Db, from: FileId, specifier: &str) -> Option<FileId> {
  db.module_resolution_input_ref(from, specifier)
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
  panic_if_cancelled(db);
  let mut files: Vec<_> = all_files(db).iter().copied().collect();
  files.sort_by_key(|f| f.0);

  let mut map = BTreeMap::new();
  for file in files {
    panic_if_cancelled(db);
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
  panic_if_cancelled(db);
  let mut files: Vec<_> = all_files(db).iter().copied().collect();
  files.sort_by_key(|f| f.0);

  let mut map = BTreeMap::new();
  for file in files {
    panic_if_cancelled(db);
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
  if child == parent {
    return;
  }

  match map.get(&child) {
    None => {
      map.insert(child, parent);
    }
    Some(existing) if *existing == parent => {}
    Some(existing) => {
      // Keep the first observed parent edge (deterministic iteration) and log the conflict.
      tracing::debug!(
        ?child,
        ?existing,
        ?parent,
        "ignoring conflicting body parent edge"
      );
    }
  }
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

  fn hir_body_range(lowered: &LowerResult, body: &hir_js::Body) -> TextRange {
    let mut start = u32::MAX;
    let mut end = 0u32;
    for stmt in body.stmts.iter() {
      start = start.min(stmt.span.start);
      end = end.max(stmt.span.end);
    }
    for expr in body.exprs.iter() {
      start = start.min(expr.span.start);
      end = end.max(expr.span.end);
    }
    for pat in body.pats.iter() {
      start = start.min(pat.span.start);
      end = end.max(pat.span.end);
    }

    if start == u32::MAX {
      // Prefer the stored body span for synthesized bodies (notably initializer bodies) that
      // don't contain nested statement/expression spans.
      match body.kind {
        hir_js::BodyKind::Class => TextRange::new(0, 0),
        _ => {
          if body.span.start != body.span.end {
            body.span
          } else {
            lowered
              .def(body.owner)
              .map(|def| def.span)
              .unwrap_or_else(|| TextRange::new(0, 0))
          }
        }
      }
    } else {
      TextRange::new(start, end)
    }
  }

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

  // Bodies synthesized for definitions (notably variable initializers) may not
  // be referenced directly by `StmtKind::Decl` or expression nodes in the
  // surrounding body. Link them through the definition parent chain so nested
  // checks can seed outer bindings.
  let mut def_to_body: BTreeMap<hir_js::DefId, hir_js::BodyId> = BTreeMap::new();
  for def in lowered.defs.iter() {
    if let Some(body) = def.body {
      def_to_body.insert(def.id, body);
    }
  }
  for def in lowered.defs.iter() {
    let Some(child_body) = def.body else {
      continue;
    };
    if child_body == root_body {
      continue;
    }
    let Some(parent_def) = def.parent else {
      continue;
    };
    let Some(parent_body) = def_to_body.get(&parent_def).copied() else {
      continue;
    };
    if child_body == parent_body {
      continue;
    }
    parents.entry(child_body).or_insert(parent_body);
  }

  // Fallback: infer missing parent links from body span containment.
  //
  // `hir-js` synthesizes bodies for initializer expressions (and similar nodes) that are not
  // referenced by the surrounding statement list. Those bodies still need parent edges so nested
  // checks can seed parameter/local bindings.
  let mut body_ranges: Vec<(BodyId, TextRange)> = lowered
    .body_index
    .keys()
    .copied()
    .filter_map(|id| lowered.body(id).map(|b| (id, hir_body_range(lowered, b))))
    .collect();
  body_ranges.sort_by_key(|(id, range)| (range.start, Reverse(range.end), id.0));

  let mut stack: Vec<(BodyId, TextRange)> = Vec::new();
  for (child, range) in body_ranges {
    if child == root_body {
      stack.clear();
      stack.push((child, range));
      continue;
    }

    while let Some((_, parent_range)) = stack.last().copied() {
      if range.start >= parent_range.start && range.end <= parent_range.end {
        break;
      }
      stack.pop();
    }

    let computed_parent = stack.last().map(|(id, _)| *id).unwrap_or(root_body);
    if computed_parent != child {
      let is_initializer = lowered
        .body(child)
        .map(|body| matches!(body.kind, hir_js::BodyKind::Initializer))
        .unwrap_or(false);
      if is_initializer || !parents.contains_key(&child) {
        parents.insert(child, computed_parent);
      }
    }
    stack.push((child, range));
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

/// Mapping from a definition to its initializer expression within HIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VarInit {
  /// Body containing the variable declarator.
  pub body: BodyId,
  /// Expression representing the initializer.
  pub expr: ExprId,
  /// Decl kind (`var`/`let`/`const`) of the declarator.
  pub decl_kind: VarDeclKind,
  /// Pattern bound by the declarator, if available.
  pub pat: Option<PatId>,
  /// Span covering the binding pattern, if available.
  pub span: Option<TextRange>,
}

fn span_distance(a: TextRange, b: TextRange) -> u64 {
  let start = a.start.abs_diff(b.start) as u64;
  let end = a.end.abs_diff(b.end) as u64;
  start.saturating_add(end)
}

pub fn var_initializer(db: &dyn Db, def: DefId) -> Option<VarInit> {
  let file = def_file(db, def)?;
  let lowered = lower_hir(db, file);
  let lowered = lowered.lowered.as_deref()?;
  let hir_def = lowered.def(def)?;
  let def_span = hir_def.span;
  let def_name = lowered.names.resolve(hir_def.path.name);
  var_initializer_in_file(lowered, def, def_span, def_name)
}

pub(crate) fn var_initializer_in_file(
  lowered: &LowerResult,
  def: DefId,
  def_span: TextRange,
  def_name: Option<&str>,
) -> Option<VarInit> {
  let hir_def = lowered.def(def)?;
  match hir_def.path.kind {
    DefKind::Var | DefKind::VarDeclarator => {}
    DefKind::Field | DefKind::Param => return None,
    _ if def_name != Some("default") => return None,
    _ => {}
  }

  fn find_pat_by_span(body: &hir_js::Body, pat: PatId, target: TextRange) -> Option<PatId> {
    let pat_data = body.pats.get(pat.0 as usize)?;
    if pat_data.span == target {
      return Some(pat);
    }
    match &pat_data.kind {
      PatKind::Ident(_) | PatKind::AssignTarget(_) => None,
      PatKind::Array(arr) => {
        for elem in arr.elements.iter() {
          let Some(elem) = elem.as_ref() else {
            continue;
          };
          if let Some(found) = find_pat_by_span(body, elem.pat, target) {
            return Some(found);
          }
        }
        if let Some(rest) = arr.rest {
          if let Some(found) = find_pat_by_span(body, rest, target) {
            return Some(found);
          }
        }
        None
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          if let Some(found) = find_pat_by_span(body, prop.value, target) {
            return Some(found);
          }
        }
        if let Some(rest) = obj.rest {
          if let Some(found) = find_pat_by_span(body, rest, target) {
            return Some(found);
          }
        }
        None
      }
      PatKind::Rest(inner) => find_pat_by_span(body, **inner, target),
      PatKind::Assign { target: inner, .. } => find_pat_by_span(body, *inner, target),
    }
  }

  fn collect_named_ident_pats(
    lowered: &LowerResult,
    body: &hir_js::Body,
    pat: PatId,
    name: &str,
    traversal_idx: &mut usize,
    out: &mut Vec<(PatId, TextRange, usize)>,
  ) {
    let Some(pat_data) = body.pats.get(pat.0 as usize) else {
      return;
    };
    let idx = *traversal_idx;
    *traversal_idx += 1;
    if let PatKind::Ident(name_id) = &pat_data.kind {
      if lowered.names.resolve(*name_id) == Some(name) {
        out.push((pat, pat_data.span, idx));
      }
    }
    match &pat_data.kind {
      PatKind::Ident(_) | PatKind::AssignTarget(_) => {}
      PatKind::Array(arr) => {
        for elem in arr.elements.iter() {
          let Some(elem) = elem.as_ref() else {
            continue;
          };
          collect_named_ident_pats(lowered, body, elem.pat, name, traversal_idx, out);
        }
        if let Some(rest) = arr.rest {
          collect_named_ident_pats(lowered, body, rest, name, traversal_idx, out);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          collect_named_ident_pats(lowered, body, prop.value, name, traversal_idx, out);
        }
        if let Some(rest) = obj.rest {
          collect_named_ident_pats(lowered, body, rest, name, traversal_idx, out);
        }
      }
      PatKind::Rest(inner) => {
        collect_named_ident_pats(lowered, body, **inner, name, traversal_idx, out)
      }
      PatKind::Assign { target, .. } => {
        collect_named_ident_pats(lowered, body, *target, name, traversal_idx, out)
      }
    }
  }

  // Prefer initializer bodies over containing statements when multiple HIR bodies contain the same
  // initializer span (e.g. the main `TopLevel` body and the synthesized `Initializer` body). Using
  // the initializer body yields more deterministic typing: external bindings can be seeded from
  // the ambient environment rather than relying on flow state built up by earlier statements in
  // the top-level body.
  let mut best: Option<((u8, u64), (usize, usize, usize, usize, u32), VarInit)> = None;

  for (body_order, (body_id, _)) in lowered.body_index.iter().enumerate() {
    let body = lowered.body(*body_id)?;
    let body_kind_rank = match body.kind {
      hir_js::BodyKind::Initializer => 0,
      hir_js::BodyKind::TopLevel => 1,
      hir_js::BodyKind::Function => 2,
      hir_js::BodyKind::Class => 3,
      hir_js::BodyKind::Unknown => 4,
    };
    for (stmt_idx, stmt) in body.stmts.iter().enumerate() {
      let decl = match &stmt.kind {
        StmtKind::Var(decl) => decl,
        _ => continue,
      };
      for (decl_idx, declarator) in decl.declarators.iter().enumerate() {
        let Some(expr) = declarator.init else {
          continue;
        };
        if let Some(found_pat) = find_pat_by_span(body, declarator.pat, def_span) {
          let span = body.pats.get(found_pat.0 as usize).map(|p| p.span)?;
          let candidate = VarInit {
            body: *body_id,
            expr,
            decl_kind: decl.kind,
            pat: Some(found_pat),
            span: Some(span),
          };
          let key = (
            (body_kind_rank, 0),
            (
              body_order,
              stmt_idx,
              decl_idx,
              // `found_pat` is an exact span match, so traversal order is irrelevant; keep the
              // key stable by using `0` here and breaking ties with the pat id.
              0,
              found_pat.0,
            ),
          );
          let replace = best
            .as_ref()
            .map(|current| key < (current.0, current.1))
            .unwrap_or(true);
          if replace {
            best = Some((key.0, key.1, candidate));
          }
          continue;
        }

        let Some(name) = def_name else {
          continue;
        };
        let mut candidates = Vec::new();
        let mut traversal_idx = 0usize;
        collect_named_ident_pats(
          lowered,
          body,
          declarator.pat,
          name,
          &mut traversal_idx,
          &mut candidates,
        );
        for (candidate_pat, span, traversal_idx) in candidates {
          let dist = span_distance(span, def_span);
          let key = (
            (body_kind_rank, dist),
            (
              body_order,
              stmt_idx,
              decl_idx,
              traversal_idx,
              candidate_pat.0,
            ),
          );
          let candidate = VarInit {
            body: *body_id,
            expr,
            decl_kind: decl.kind,
            pat: Some(candidate_pat),
            span: Some(span),
          };
          let replace = best
            .as_ref()
            .map(|current| key < (current.0, current.1))
            .unwrap_or(true);
          if replace {
            best = Some((key.0, key.1, candidate));
          }
        }
      }
    }
  }

  if let Some((_, _, init)) = best {
    return Some(init);
  }

  if def_name == Some("default") {
    for export in lowered.hir.exports.iter() {
      if let ExportKind::Default(default) = &export.kind {
        if let ExportDefaultValue::Expr { expr, body } = &default.value {
          if export.span == def_span
            || (export.span.start <= def_span.start && def_span.end <= export.span.end)
          {
            return Some(VarInit {
              body: *body,
              expr: *expr,
              decl_kind: VarDeclKind::Const,
              pat: None,
              span: Some(export.span),
            });
          }
        }
      }
    }
  }

  None
}

#[salsa::input]
pub struct TypeCompilerOptions {
  #[return_ref]
  pub options: CompilerOptions,
}

#[salsa::input]
pub struct TypeStoreInput {
  pub store: SharedTypeStore,
}

#[salsa::input]
pub struct FilesInput {
  #[return_ref]
  pub files: Arc<Vec<FileId>>,
}

#[salsa::input]
pub struct DeclTypesInput {
  pub file: FileId,
  #[return_ref]
  pub decls: Arc<BTreeMap<DefId, DeclInfo>>,
}

#[salsa::db]
pub trait TypeDb: salsa::Database + Send + 'static {
  fn compiler_options_input(&self) -> TypeCompilerOptions;
  fn type_store_input(&self) -> TypeStoreInput;
  fn files_input(&self) -> FilesInput;
  fn decl_types_input(&self, file: FileId) -> Option<DeclTypesInput>;
  fn profiler(&self) -> Option<QueryStatsCollector>;
  fn body_cache(&self) -> &BodyCache;
  fn def_cache(&self) -> &DefCache;
}

/// Cheap wrapper around [`TypeStore`] with pointer-based equality for salsa
/// inputs.
#[derive(Clone)]
pub struct SharedTypeStore(pub Arc<TypeStore>);

impl SharedTypeStore {
  pub fn arc(&self) -> Arc<TypeStore> {
    Arc::clone(&self.0)
  }
}

impl fmt::Debug for SharedTypeStore {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("SharedTypeStore")
      .field(&Arc::as_ptr(&self.0))
      .finish()
  }
}

impl PartialEq for SharedTypeStore {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.0, &other.0)
  }
}

impl Eq for SharedTypeStore {}

/// Kind of declaration associated with a definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
  Var,
  Function,
  TypeAlias,
  Interface,
  Namespace,
}

/// Representation of a lowered declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclInfo {
  /// Owning file.
  pub file: FileId,
  /// Name of the declaration, used for merging.
  pub name: String,
  /// Kind of declaration (variable/function/etc.).
  pub kind: DeclKind,
  /// Explicitly annotated type if present.
  pub declared_type: Option<TypeId>,
  /// Initializer used for inference if no annotation is present.
  pub initializer: Option<Initializer>,
}

/// Simplified initializer model used by [`check_body`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Initializer {
  /// Reference to another definition.
  Reference(DefId),
  /// Explicit type literal for the initializer.
  Type(TypeId),
  /// Union-like combination of other initializers.
  Union(Vec<Initializer>),
}

/// Semantic snapshot derived from declared definitions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeSemantics {
  /// Grouped definitions by merge boundary (currently name + file).
  pub merged_defs: HashMap<DefId, Arc<Vec<DefId>>>,
  /// Owning file for each known definition.
  pub def_files: HashMap<DefId, FileId>,
}

#[salsa::tracked]
pub fn type_compiler_options(db: &dyn TypeDb) -> CompilerOptions {
  db.compiler_options_input().options(db).clone()
}

#[salsa::tracked]
pub fn type_store(db: &dyn TypeDb) -> SharedTypeStore {
  db.type_store_input().store(db)
}

#[salsa::tracked]
pub fn files(db: &dyn TypeDb) -> Arc<Vec<FileId>> {
  db.files_input().files(db).clone()
}

#[salsa::tracked]
pub fn decl_types_in_file(
  db: &dyn TypeDb,
  file: FileId,
  _seed: (),
) -> Arc<BTreeMap<DefId, DeclInfo>> {
  // The unit `seed` keeps this as a memoized-style query without requiring
  // `FileId` to be a salsa struct.
  db.decl_types_input(file)
    .map(|handle| handle.decls(db).clone())
    .unwrap_or_else(|| Arc::new(BTreeMap::new()))
}

#[salsa::tracked]
pub fn type_semantics(db: &dyn TypeDb) -> Arc<TypeSemantics> {
  let mut by_name: BTreeMap<(FileId, String), Vec<DefId>> = BTreeMap::new();
  let mut def_files = HashMap::new();
  let mut file_list: Vec<_> = files(db).iter().copied().collect();
  file_list.sort_by_key(|f| f.0);
  for file in file_list.into_iter() {
    for (def, decl) in decl_types_in_file(db, file, ()).iter() {
      by_name
        .entry((decl.file, decl.name.clone()))
        .or_default()
        .push(*def);
      def_files.insert(*def, decl.file);
    }
  }

  let mut merged_defs = HashMap::new();
  for (_, mut defs) in by_name.into_iter() {
    defs.sort_by_key(|d| d.0);
    let group = Arc::new(defs.clone());
    for def in defs {
      merged_defs.insert(def, Arc::clone(&group));
    }
  }

  Arc::new(TypeSemantics {
    merged_defs,
    def_files,
  })
}

/// Snapshot cache statistics for the tracked `check_body` and `type_of_def`
/// queries. Statistics are also recorded into the active profiler, if present,
/// so callers can observe cache activity alongside other query metrics.
pub fn cache_stats(db: &dyn TypeDb) -> (CacheStats, CacheStats) {
  let body = db.body_cache().stats();
  let def = db.def_cache().stats();
  if let Some(profiler) = db.profiler() {
    profiler.record_cache(CacheKind::Body, &body);
    profiler.record_cache(CacheKind::Def, &def);
  }
  (body, def)
}

fn cached_check_body(db: &dyn TypeDb, def: DefId) -> TypeId {
  let store = type_store(db).arc();
  let primitives = store.primitive_ids();
  let revision = current_revision(db);
  let profiler = db.profiler();
  let cache_before = profiler.as_ref().map(|_| db.body_cache().stats());
  if let Some(cached) = db.body_cache().get(def, revision) {
    if let Some(profiler) = profiler.as_ref() {
      profiler.record(QueryKind::CheckBody, true, Duration::ZERO);
      if let Some(before) = cache_before.as_ref() {
        let after = db.body_cache().stats();
        profiler.record_cache(CacheKind::Body, &cache_delta(&after, before));
      }
    }
    return cached;
  }

  let Some(decl) = decl_types_for_def(db, def) else {
    return primitives.unknown;
  };
  let Some(init) = decl.initializer.clone() else {
    return primitives.unknown;
  };

  let _timer = profiler
    .as_ref()
    .map(|profiler| profiler.timer(QueryKind::CheckBody, false));
  let result = eval_initializer(db, &store, init);
  db.body_cache().insert(def, revision, result);
  if let Some(profiler) = profiler.as_ref() {
    if let Some(before) = cache_before.as_ref() {
      let after = db.body_cache().stats();
      profiler.record_cache(CacheKind::Body, &cache_delta(&after, before));
    }
  }
  result
}

#[salsa::tracked(recovery_fn = check_body_cycle, lru = 0)]
pub fn check_body(db: &dyn TypeDb, def: DefId, _seed: ()) -> TypeId {
  // The unit seed mirrors `decl_types_in_file` to avoid introducing synthetic
  // salsa structs for every definition key.
  cached_check_body(db, def)
}

fn check_body_cycle(db: &dyn TypeDb, _cycle: &salsa::Cycle, _def: DefId, _seed: ()) -> TypeId {
  // Bodies are part of the same cycle when an initializer references its own
  // definition. Recover with `any` to mirror `type_of_def`'s fallback and avoid
  // panicking on self-references.
  type_store(db).arc().primitive_ids().any
}

fn cached_type_of_def(db: &dyn TypeDb, def: DefId) -> TypeId {
  // The extra seed enables the tracked query to memoize arbitrary `DefId`s
  // without forcing them to implement salsa's struct traits.
  // Track compiler options changes even if we do not branch on them yet.
  let _options = type_compiler_options(db);
  let store = type_store(db).arc();
  let primitives = store.primitive_ids();
  let revision = current_revision(db);
  let profiler = db.profiler();
  let cache_before = profiler.as_ref().map(|_| db.def_cache().stats());
  if let Some(cached) = db.def_cache().get(def, revision) {
    if let Some(profiler) = profiler.as_ref() {
      profiler.record(QueryKind::TypeOfDef, true, Duration::ZERO);
      if let Some(before) = cache_before.as_ref() {
        let after = db.def_cache().stats();
        profiler.record_cache(CacheKind::Def, &cache_delta(&after, before));
      }
    }
    return cached;
  }

  let _timer = profiler
    .as_ref()
    .map(|profiler| profiler.timer(QueryKind::TypeOfDef, false));
  let base = base_type(db, &store, def, primitives.any);

  let mut result = base;
  let semantics = type_semantics(db);
  if let Some(group) = semantics.merged_defs.get(&def) {
    if group.len() > 1 {
      let mut members = Vec::with_capacity(group.len());
      for member in group.iter() {
        // Avoid recursive `type_of_def` calls across a merged group by using
        // each member's base type directly. Definitions are processed in the
        // stable order produced by `type_semantics` to keep unions deterministic.
        let ty = if *member == def {
          base
        } else {
          base_type(db, &store, *member, primitives.any)
        };
        members.push(ty);
      }
      result = store.union(members);
    }
  }

  db.def_cache().insert(def, revision, result);
  if let Some(profiler) = profiler.as_ref() {
    if let Some(before) = cache_before.as_ref() {
      let after = db.def_cache().stats();
      profiler.record_cache(CacheKind::Def, &cache_delta(&after, before));
    }
  }
  result
}

#[salsa::tracked(recovery_fn = type_of_def_cycle, lru = 0)]
pub fn type_of_def(db: &dyn TypeDb, def: DefId, _seed: ()) -> TypeId {
  cached_type_of_def(db, def)
}

fn type_of_def_cycle(db: &dyn TypeDb, _cycle: &salsa::Cycle, _def: DefId, _seed: ()) -> TypeId {
  // Self-referential definitions fall back to `any` to keep results stable
  // under cycles instead of panicking.
  type_store(db).arc().primitive_ids().any
}

fn base_type(db: &dyn TypeDb, store: &Arc<TypeStore>, def: DefId, fallback: TypeId) -> TypeId {
  if let Some(decl) = decl_types_for_def(db, def) {
    if let Some(annotated) = decl.declared_type {
      return store.canon(annotated);
    }
    if decl.initializer.is_some() {
      return check_body(db, def, ());
    }
  }
  fallback
}

fn decl_types_for_def(db: &dyn TypeDb, def: DefId) -> Option<DeclInfo> {
  let semantics = type_semantics(db);
  if let Some(file) = semantics.def_files.get(&def).copied() {
    if let Some(entry) = decl_types_in_file(db, file, ()).get(&def) {
      return Some(entry.clone());
    }
  }

  let mut file_list: Vec<_> = files(db).iter().copied().collect();
  file_list.sort_by_key(|f| f.0);
  for file in file_list {
    if let Some(entry) = decl_types_in_file(db, file, ()).get(&def) {
      return Some(entry.clone());
    }
  }
  None
}

fn eval_initializer(db: &dyn TypeDb, store: &Arc<TypeStore>, init: Initializer) -> TypeId {
  match init {
    Initializer::Reference(def) => type_of_def(db, def, ()),
    Initializer::Type(ty) => store.canon(ty),
    Initializer::Union(inits) => {
      let mut members = Vec::with_capacity(inits.len());
      for init in inits.into_iter() {
        members.push(eval_initializer(db, store, init));
      }
      store.union(members)
    }
  }
}

pub trait TypeDatabase: TypeDb {}
impl TypeDatabase for TypesDatabase {}

#[salsa::db]
#[derive(Clone)]
pub struct TypesDatabase {
  storage: salsa::Storage<Self>,
  compiler_options: Option<TypeCompilerOptions>,
  type_store: Option<TypeStoreInput>,
  files: Option<FilesInput>,
  decls: BTreeMap<FileId, DeclTypesInput>,
  profiler: Option<QueryStatsCollector>,
  body_cache: BodyCache,
  def_cache: DefCache,
}

impl Default for TypesDatabase {
  fn default() -> Self {
    let cache_options = CompilerOptions::default().cache;
    Self {
      storage: salsa::Storage::default(),
      compiler_options: None,
      type_store: None,
      files: None,
      decls: BTreeMap::new(),
      profiler: None,
      body_cache: BodyCache::new(cache_options.body_config()),
      def_cache: DefCache::new(cache_options.def_config()),
    }
  }
}

#[salsa::db]
impl salsa::Database for TypesDatabase {
  fn salsa_event(&self, _event: &dyn Fn() -> salsa::Event) {}
}

#[salsa::db]
impl TypeDb for TypesDatabase {
  fn compiler_options_input(&self) -> TypeCompilerOptions {
    self
      .compiler_options
      .expect("compiler options must be initialized")
  }

  fn type_store_input(&self) -> TypeStoreInput {
    self.type_store.expect("type store must be initialized")
  }

  fn files_input(&self) -> FilesInput {
    self.files.expect("files must be initialized")
  }

  fn decl_types_input(&self, file: FileId) -> Option<DeclTypesInput> {
    self.decls.get(&file).copied()
  }

  fn profiler(&self) -> Option<QueryStatsCollector> {
    self.profiler.clone()
  }

  fn body_cache(&self) -> &BodyCache {
    &self.body_cache
  }

  fn def_cache(&self) -> &DefCache {
    &self.def_cache
  }
}

impl TypesDatabase {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn snapshot(&self) -> Self {
    self.clone()
  }

  fn configure_cache_limits(&mut self, cache: &CacheOptions) {
    self.body_cache = BodyCache::new(cache.body_config());
    self.def_cache = DefCache::new(cache.def_config());
  }

  pub fn set_compiler_options(&mut self, options: CompilerOptions) {
    self.configure_cache_limits(&options.cache);
    if let Some(handle) = self.compiler_options {
      handle.set_options(self).to(options);
    } else {
      self.compiler_options = Some(TypeCompilerOptions::new(self, options));
    }
  }

  pub fn set_type_store(&mut self, store: SharedTypeStore) {
    if let Some(handle) = self.type_store {
      handle.set_store(self).to(store.clone());
    } else {
      self.type_store = Some(TypeStoreInput::new(self, store));
    }
  }

  pub fn set_files(&mut self, files: Arc<Vec<FileId>>) {
    if let Some(handle) = self.files {
      handle.set_files(self).to(files);
    } else {
      self.files = Some(FilesInput::new(self, files));
    }
  }

  pub fn set_decl_types_in_file(&mut self, file: FileId, decls: Arc<BTreeMap<DefId, DeclInfo>>) {
    if let Some(handle) = self.decls.get(&file).copied() {
      handle.set_decls(self).to(decls);
    } else {
      let input = DeclTypesInput::new(self, file, decls);
      self.decls.insert(file, input);
    }
  }

  pub fn set_profiler(&mut self, profiler: QueryStatsCollector) {
    self.profiler = Some(profiler);
  }
}

/// Canonicalize and deduplicate diagnostics to keep outputs deterministic.
pub fn aggregate_diagnostics(mut diagnostics: Vec<Diagnostic>) -> Arc<[Diagnostic]> {
  codes::normalize_diagnostics(&mut diagnostics);
  diagnostics.sort_by(|a, b| {
    (
      a.primary.file,
      a.primary.range.start,
      a.code.as_str(),
      &a.message,
      a.primary.range.end,
      a.severity,
    )
      .cmp(&(
        b.primary.file,
        b.primary.range.start,
        b.code.as_str(),
        &b.message,
        b.primary.range.end,
        b.severity,
      ))
  });
  diagnostics.dedup();
  diagnostics.into()
}

/// Aggregate diagnostics from all pipeline stages.
pub fn aggregate_program_diagnostics(
  parse: impl IntoIterator<Item = Diagnostic>,
  lower: impl IntoIterator<Item = Diagnostic>,
  semantic: impl IntoIterator<Item = Diagnostic>,
  bodies: impl IntoIterator<Item = Diagnostic>,
) -> Arc<[Diagnostic]> {
  let mut diagnostics: Vec<_> = parse.into_iter().collect();
  diagnostics.extend(lower);
  diagnostics.extend(semantic);
  diagnostics.extend(bodies);
  aggregate_diagnostics(diagnostics)
}

#[salsa::tracked]
fn extra_diagnostics_for(db: &dyn Db) -> Arc<[Diagnostic]> {
  db.extra_diagnostics_input()
    .map(|input| input.diagnostics(db).clone())
    .unwrap_or_else(|| Arc::from([]))
}

fn body_diagnostics_from_results(db: &dyn Db, body: BodyId) -> Arc<[Diagnostic]> {
  db.body_result(body)
    .map(|result| Arc::from(result.diagnostics.clone().into_boxed_slice()))
    .unwrap_or_else(|| Arc::from([]))
}

#[salsa::tracked]
fn program_diagnostics_for(db: &dyn Db) -> Arc<[Diagnostic]> {
  panic_if_cancelled(db);
  let files = all_files(db);
  let mut parse_diags = Vec::new();
  let mut lower_diags = Vec::new();
  let mut module_diags = Vec::new();
  for file in files.iter() {
    panic_if_cancelled(db);
    let parsed = parse(db, *file);
    parse_diags.extend(parsed.diagnostics.into_iter());
    let lowered = lower_hir(db, *file);
    lower_diags.extend(lowered.diagnostics.into_iter());
    module_diags.extend(unresolved_module_diagnostics(db, *file).iter().cloned());
  }
  let semantics = ts_semantics(db);
  let mut body_diags = Vec::new();
  for (body, file) in body_to_file(db).iter() {
    panic_if_cancelled(db);
    if matches!(file_kind(db, *file), FileKind::Dts) {
      continue;
    }
    body_diags.extend(body_diagnostics_from_results(db, *body).iter().cloned());
  }
  body_diags.extend(extra_diagnostics_for(db).iter().cloned());
  // Drop binder-level unresolved import diagnostics (`BIND1002`) in favor of the
  // module-resolution-based `UNRESOLVED_MODULE` diagnostics, which carry spans
  // targeting the specifier literal.
  let semantic_diags = semantics
    .diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() != "BIND1002")
    .cloned()
    .chain(module_diags.into_iter());
  aggregate_program_diagnostics(parse_diags, lower_diags, semantic_diags, body_diags)
}

/// Derived query that aggregates diagnostics from parsing, lowering, binding,
/// and body checking across all reachable files.
pub fn program_diagnostics(db: &dyn Db) -> Arc<[Diagnostic]> {
  program_diagnostics_for(db)
}
