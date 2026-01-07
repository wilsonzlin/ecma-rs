extern crate semantic_js as semantic_js_crate;

use crate::api::{BodyId, DefId, Diagnostic, ExprId, FileId, FileKey, PatId, Span, TextRange};
use crate::db::spans::expr_at_from_spans;
use crate::semantic_js;
use crate::{SymbolBinding, SymbolInfo, SymbolOccurrence};
use ahash::AHashSet;
use hir_js::ids::{MISSING_BODY, MISSING_DEF};
use hir_js::{
  BodyKind as HirBodyKind, DefId as HirDefId, DefKind as HirDefKind, ExportKind as HirExportKind,
  ExprKind as HirExprKind, LowerResult, NameId, PatId as HirPatId, PatKind as HirPatKind,
  VarDeclKind as HirVarDeclKind,
};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjVal};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::Func;
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{FuncDecl, ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{ImportEqualsRhs, NamespaceBody};
use parse_js::ast::type_expr::{
  TypeArray, TypeEntityName, TypeExpr, TypeLiteral, TypeMember, TypePropertyKey, TypeUnion,
};
use parse_js::loc::Loc;
use semantic_js_crate::ts as sem_ts;
use std::cmp::Reverse;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use types_ts_interned::{self as tti, PropData, PropKey, Property, RelateCtx, TypeId, TypeParamId};

use self::check::caches::{CheckerCacheStats, CheckerCaches};
use self::check::flow_bindings::FlowBindings;
use self::check::relate_hooks;
use crate::check::expr::{resolve_call, resolve_construct};
use crate::check::overload::{callable_signatures, CallArgType};
use crate::check::type_expr::{TypeLowerer, TypeResolver};
use crate::codes;
use crate::db::queries::{var_initializer_in_file, VarInit};
use crate::db::{self, BodyCheckContext, BodyCheckDb, BodyInfo, GlobalBindingsDb};
use crate::expand::ProgramTypeExpander as RefExpander;
use crate::files::{FileOrigin, FileRegistry};
use crate::profile::{QueryKind, QueryStatsCollector};
use crate::triple_slash::{
  normalize_reference_path_specifier, scan_triple_slash_directives, TripleSlashReferenceKind,
};
use crate::type_queries::{PropertyKey, TypeQueries};
use crate::{FatalError, HostError, IceContext};

#[path = "../check/mod.rs"]
pub(crate) mod check;

#[macro_use]
#[path = "query_span.rs"]
mod query_span;

use self::query_span::QuerySpan;

#[path = "legacy_types.rs"]
mod legacy_types;

pub use legacy_types::{BuiltinTypes, TypeStore};
pub(crate) use legacy_types::{ObjectProperty, ObjectType, TypeKind};

#[path = "exports.rs"]
mod exports;

use exports::{ExportAll, FileState, Reexport};
pub use exports::{ExportEntry, ExportMap};

#[path = "defs.rs"]
mod defs;

pub use defs::*;

#[path = "sem_hir_builder.rs"]
mod sem_hir_builder;

use sem_hir_builder::{
  alloc_synthetic_def_id, match_kind_from_def, match_kind_from_hir, BodyMeta, DefMatchKind,
  SemHirBuilder,
};

#[path = "types.rs"]
mod types;

use types::{
  callable_return_is_unknown, convert_type_for_display, display_type_from_state,
  export_assignment_path_for_file, lookup_interned_property_type, DeclTypeResolver,
  ProgramTypeExpander,
};
pub use types::{ExplainTree, TypeDisplay};
pub(crate) use types::{NamespaceMemberIndex, ProgramTypeResolver};

#[cfg(feature = "serde")]
#[path = "snapshot.rs"]
mod snapshot;

use crate::lib_support::lib_env::{collect_libs, validate_libs};
use crate::lib_support::{
  CacheMode, CacheOptions, CompilerOptions, FileKind, LibFile, LibManager, ModuleKind, ScriptTarget,
};

#[path = "api.rs"]
mod api;

use api::body_extent_from_spans;
pub use api::{BodyCheckResult, Host, Program};

mod analysis;
mod bind;
mod bodies;
mod decl_types;
mod inputs;
mod interned;
mod legacy_type_expr;
mod merging;
mod module_exports;
mod span_types;
mod type_ops;

fn sem_file_kind(kind: FileKind) -> sem_ts::FileKind {
  match kind {
    FileKind::Dts => sem_ts::FileKind::Dts,
    _ => sem_ts::FileKind::Ts,
  }
}

#[derive(Clone)]
struct CachedBodyCheckContext {
  revision: salsa::Revision,
  cache_options: CacheOptions,
  context: Arc<BodyCheckContext>,
}

#[derive(Clone, Debug)]
struct ImportAssignmentRequireRecord {
  file: FileId,
  span: TextRange,
  target: ImportTarget,
}

struct ProgramState {
  analyzed: bool,
  snapshot_loaded: bool,
  cancelled: Arc<AtomicBool>,
  host: Arc<dyn Host>,
  lib_manager: Arc<LibManager>,
  compiler_options: CompilerOptions,
  compiler_options_override: Option<CompilerOptions>,
  file_overrides: HashMap<FileKey, Arc<str>>,
  decl_types_fingerprint: Option<u64>,
  cached_body_context: Option<CachedBodyCheckContext>,
  typecheck_db: db::TypecheckDb,
  checker_caches: CheckerCaches,
  cache_stats: CheckerCacheStats,
  asts: HashMap<FileId, Arc<Node<TopLevel>>>,
  ast_indexes: HashMap<FileId, Arc<check::hir_body::AstIndex>>,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_map: HashMap<BodyId, BodyMeta>,
  body_owners: HashMap<BodyId, DefId>,
  body_parents: HashMap<BodyId, BodyId>,
  hir_lowered: HashMap<FileId, Arc<LowerResult>>,
  local_semantics: HashMap<FileId, sem_ts::locals::TsLocalSemantics>,
  semantics: Option<Arc<sem_ts::TsProgramSemantics>>,
  qualified_def_members: Arc<HashMap<(DefId, String, sem_ts::Namespace), DefId>>,
  def_types: HashMap<DefId, TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  checking_bodies: HashSet<BodyId>,
  symbol_to_def: HashMap<semantic_js::SymbolId, DefId>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  local_symbol_info: BTreeMap<semantic_js::SymbolId, crate::db::symbols::LocalSymbolInfo>,
  file_registry: FileRegistry,
  file_kinds: HashMap<FileId, FileKind>,
  lib_file_ids: HashSet<FileId>,
  lib_texts: HashMap<FileId, Arc<str>>,
  lib_diagnostics: Vec<Diagnostic>,
  root_ids: Vec<FileId>,
  global_bindings: Arc<BTreeMap<String, SymbolBinding>>,
  namespace_object_types: HashMap<(FileId, String), (tti::TypeId, TypeId)>,
  module_namespace_defs: HashMap<FileId, DefId>,
  module_namespace_types: HashMap<FileId, TypeId>,
  module_namespace_in_progress: HashSet<FileId>,
  namespace_member_index: Option<Arc<NamespaceMemberIndex>>,
  callable_overloads: HashMap<(FileId, String), Vec<DefId>>,
  import_assignment_requires: Vec<ImportAssignmentRequireRecord>,
  diagnostics: Vec<Diagnostic>,
  implicit_any_reported: HashSet<Span>,
  type_store: TypeStore,
  interned_store: Option<Arc<tti::TypeStore>>,
  interned_def_types: HashMap<DefId, tti::TypeId>,
  interned_named_def_types: HashMap<tti::TypeId, DefId>,
  interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
  interned_type_param_decls: HashMap<DefId, Arc<[tti::TypeParamDecl]>>,
  interned_intrinsics: HashMap<DefId, tti::IntrinsicKind>,
  interned_class_instances: HashMap<DefId, tti::TypeId>,
  value_defs: HashMap<DefId, DefId>,
  builtin: BuiltinTypes,
  query_stats: QueryStatsCollector,
  current_file: Option<FileId>,
  next_def: u64,
  next_body: u64,
  next_symbol: u32,
  type_stack: Vec<DefId>,
}

impl GlobalBindingsDb for ProgramState {
  fn ts_semantics(&self) -> Option<Arc<sem_ts::TsProgramSemantics>> {
    self.semantics.clone()
  }

  fn dts_value_bindings(&self) -> Vec<(String, SymbolBinding)> {
    let mut bindings = Vec::new();
    let semantics = self.semantics.as_deref();
    for (file, state) in self.files.iter() {
      if self.file_kinds.get(file) != Some(&FileKind::Dts) {
        continue;
      }
      for (name, binding) in state.bindings.iter() {
        let mut binding = binding.clone();
        if let Some(def) = binding.def {
          if let Some(ty) = self.interned_def_types.get(&def).copied() {
            binding.type_id = Some(ty);
          }
          if let Some(sem) = semantics {
            if let Some(symbol) = sem.symbol_for_def(def, sem_ts::Namespace::VALUE) {
              binding.symbol = symbol.into();
            }
          }
        }
        bindings.push((name.clone(), binding));
      }
    }
    bindings
  }

  fn type_of_def(&self, def: DefId) -> Option<TypeId> {
    self.interned_def_types.get(&def).copied()
  }

  fn primitive_ids(&self) -> Option<tti::PrimitiveIds> {
    self
      .interned_store
      .as_ref()
      .map(|store| store.primitive_ids())
  }
}

impl ProgramState {
  fn new(
    host: Arc<dyn Host>,
    lib_manager: Arc<LibManager>,
    query_stats: QueryStatsCollector,
    cancelled: Arc<AtomicBool>,
  ) -> ProgramState {
    let default_options = CompilerOptions::default();
    let (type_store, builtin) = TypeStore::new();
    let mut typecheck_db = db::TypecheckDb::default();
    typecheck_db.set_profiler(query_stats.clone());
    ProgramState {
      analyzed: false,
      snapshot_loaded: false,
      cancelled,
      host,
      lib_manager,
      compiler_options: default_options.clone(),
      compiler_options_override: None,
      file_overrides: HashMap::new(),
      decl_types_fingerprint: None,
      cached_body_context: None,
      typecheck_db,
      checker_caches: CheckerCaches::new(default_options.cache.clone()),
      cache_stats: CheckerCacheStats::default(),
      asts: HashMap::new(),
      ast_indexes: HashMap::new(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_map: HashMap::new(),
      body_owners: HashMap::new(),
      body_parents: HashMap::new(),
      hir_lowered: HashMap::new(),
      local_semantics: HashMap::new(),
      semantics: None,
      qualified_def_members: Arc::new(HashMap::new()),
      def_types: HashMap::new(),
      body_results: HashMap::new(),
      checking_bodies: HashSet::new(),
      symbol_to_def: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      local_symbol_info: BTreeMap::new(),
      file_registry: FileRegistry::new(),
      file_kinds: HashMap::new(),
      lib_file_ids: HashSet::new(),
      lib_texts: HashMap::new(),
      lib_diagnostics: Vec::new(),
      root_ids: Vec::new(),
      global_bindings: Arc::new(BTreeMap::new()),
      namespace_object_types: HashMap::new(),
      module_namespace_defs: HashMap::new(),
      module_namespace_types: HashMap::new(),
      module_namespace_in_progress: HashSet::new(),
      namespace_member_index: None,
      callable_overloads: HashMap::new(),
      import_assignment_requires: Vec::new(),
      diagnostics: Vec::new(),
      implicit_any_reported: HashSet::new(),
      type_store,
      interned_store: None,
      interned_def_types: HashMap::new(),
      interned_named_def_types: HashMap::new(),
      interned_type_params: HashMap::new(),
      interned_type_param_decls: HashMap::new(),
      interned_intrinsics: HashMap::new(),
      interned_class_instances: HashMap::new(),
      value_defs: HashMap::new(),
      builtin,
      query_stats,
      current_file: None,
      next_def: 0,
      next_body: 0,
      next_symbol: 0,
      type_stack: Vec::new(),
    }
  }

  fn reset_analysis_state(&mut self) {
    self.analyzed = false;
    self.snapshot_loaded = false;
    self.decl_types_fingerprint = None;
    self.cached_body_context = None;

    self.typecheck_db.clear_body_results();
    self.checker_caches.clear_shared();
    self.cache_stats = CheckerCacheStats::default();

    self.asts.clear();
    self.ast_indexes.clear();
    self.files.clear();
    self.def_data.clear();
    self.body_map.clear();
    self.body_owners.clear();
    self.body_parents.clear();
    self.hir_lowered.clear();
    self.local_semantics.clear();
    self.semantics = None;
    self.qualified_def_members = Arc::new(HashMap::new());
    self.def_types.clear();
    self.body_results.clear();
    self.checking_bodies.clear();
    self.symbol_to_def.clear();
    self.symbol_occurrences.clear();
    self.local_symbol_info.clear();
    self.file_registry = FileRegistry::new();
    self.file_kinds.clear();
    self.lib_file_ids.clear();
    self.lib_texts.clear();
    self.lib_diagnostics.clear();
    self.root_ids.clear();
    self.global_bindings = Arc::new(BTreeMap::new());
    self.namespace_object_types.clear();
    self.module_namespace_defs.clear();
    self.module_namespace_types.clear();
    self.module_namespace_in_progress.clear();
    self.namespace_member_index = None;
    self.callable_overloads.clear();
    self.import_assignment_requires.clear();
    self.diagnostics.clear();
    self.implicit_any_reported.clear();
    self.interned_def_types.clear();
    self.interned_named_def_types.clear();
    self.interned_type_params.clear();
    self.interned_type_param_decls.clear();
    self.interned_intrinsics.clear();
    self.interned_class_instances.clear();
    self.value_defs.clear();
    self.current_file = None;
    self.next_def = 0;
    self.next_body = 0;
    self.next_symbol = 0;
    self.type_stack.clear();

    // Match the full-reset behaviour (previously provided by `ProgramState::new`)
    // by clearing the legacy store and builtin identifiers.
    let (type_store, builtin) = TypeStore::new();
    self.type_store = type_store;
    self.builtin = builtin;
  }

  fn check_cancelled(&self) -> Result<(), FatalError> {
    if self.cancelled.load(Ordering::Relaxed) {
      Err(FatalError::Cancelled)
    } else {
      Ok(())
    }
  }

  fn push_program_diagnostic(&mut self, diagnostic: Diagnostic) {
    if diagnostic.code.as_str() == codes::IMPLICIT_ANY.as_str() {
      if !self.implicit_any_reported.insert(diagnostic.primary) {
        return;
      }
    }
    self.diagnostics.push(diagnostic);
  }

  fn set_extra_diagnostics_input(&mut self) {
    let arc: Arc<[Diagnostic]> = Arc::from(self.lib_diagnostics.clone().into_boxed_slice());
    self.typecheck_db.set_extra_diagnostics(arc);
  }

  fn file_id_for_key(&self, key: &FileKey) -> Option<FileId> {
    self.file_registry.lookup_id(key)
  }

  fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    self.file_registry.ids_for_key(key)
  }

  fn body_check_context(&mut self) -> Arc<BodyCheckContext> {
    let revision = db::db_revision(&self.typecheck_db);
    let cache_options = self.compiler_options.cache.clone();
    let store = self
      .interned_store
      .as_ref()
      .expect("interned store initialized");
    if let Some(cached) = self.cached_body_context.as_ref() {
      if cached.revision == revision
        && cached.cache_options == cache_options
        && Arc::ptr_eq(&cached.context.store, store)
      {
        return Arc::clone(&cached.context);
      }
    }

    let span = QuerySpan::enter(
      QueryKind::BuildBodyContext,
      query_span!(
        "typecheck_ts.build_body_context",
        Option::<u32>::None,
        Option::<u32>::None,
        Option::<u32>::None,
        false
      ),
      None,
      false,
      Some(self.query_stats.clone()),
    );
    let context = Arc::new(self.build_body_check_context());
    self.cached_body_context = Some(CachedBodyCheckContext {
      revision,
      cache_options,
      context: Arc::clone(&context),
    });
    if let Some(span) = span {
      span.finish(None);
    }
    context
  }

  fn build_body_check_context(&mut self) -> BodyCheckContext {
    let store = self
      .interned_store
      .as_ref()
      .expect("interned store initialized")
      .clone();
    if let Some(store) = self.interned_store.clone() {
      let mut cache = HashMap::new();
      let mut def_ids: Vec<_> = self.def_data.keys().copied().collect();
      def_ids.sort_by_key(|def| def.0);
      for def in def_ids.into_iter() {
        let needs_type = match self.interned_def_types.get(&def).copied() {
          Some(existing) => {
            matches!(store.type_kind(existing), tti::TypeKind::Unknown)
              || callable_return_is_unknown(&store, existing)
          }
          None => true,
        };
        if !needs_type {
          continue;
        }
        if std::env::var("DEBUG_MEMBER").is_ok() {
          if let Some(data) = self.def_data.get(&def) {
            eprintln!("DEBUG_MEMBER recomputing def {} {:?}", data.name, def);
          }
        }
        if let Ok(ty) = self.type_of_def(def) {
          let interned = if store.contains_type_id(ty) {
            store.canon(ty)
          } else {
            store.canon(convert_type_for_display(ty, self, &store, &mut cache))
          };
          self.interned_def_types.insert(def, interned);
        }
      }
    }
    let mut body_info = HashMap::new();
    for (id, meta) in self.body_map.iter() {
      body_info.insert(
        *id,
        BodyInfo {
          file: meta.file,
          hir: meta.hir,
          kind: meta.kind,
        },
      );
    }
    let mut file_bindings = HashMap::new();
    for (file, state) in self.files.iter() {
      file_bindings.insert(*file, state.bindings.clone());
    }
    let mut def_spans = HashMap::new();
    for (def, data) in self.def_data.iter() {
      def_spans.insert((data.file, data.span), *def);
    }
    let def_kinds = Arc::new(
      self
        .def_data
        .iter()
        .map(|(id, data)| (*id, data.kind.clone()))
        .collect(),
    );
    let def_files = Arc::new(
      self
        .def_data
        .iter()
        .map(|(id, data)| (*id, data.file))
        .collect(),
    );
    let def_id_spans = Arc::new(
      self
        .def_data
        .iter()
        .map(|(id, data)| (*id, data.span))
        .collect(),
    );
    let exports = Arc::new(
      self
        .files
        .iter()
        .map(|(file, state)| (*file, state.exports.clone()))
        .collect(),
    );
    let namespace_members = self
      .namespace_member_index
      .clone()
      .unwrap_or_else(|| Arc::new(NamespaceMemberIndex::default()));
    BodyCheckContext {
      store: Arc::clone(&store),
      target: self.compiler_options.target,
      no_implicit_any: self.compiler_options.no_implicit_any,
      use_define_for_class_fields: self.compiler_options.use_define_for_class_fields,
      interned_def_types: self.interned_def_types.clone(),
      interned_type_params: self.interned_type_params.clone(),
      interned_type_param_decls: self.interned_type_param_decls.clone(),
      interned_intrinsics: self.interned_intrinsics.clone(),
      asts: self.asts.clone(),
      lowered: self
        .hir_lowered
        .iter()
        .map(|(file, lowered)| (*file, Arc::clone(lowered)))
        .collect(),
      body_info,
      body_parents: self.body_parents.clone(),
      global_bindings: self
        .global_bindings
        .iter()
        .map(|(name, binding)| (name.clone(), binding.clone()))
        .collect(),
      file_bindings,
      def_spans,
      semantics: self.semantics.clone(),
      def_kinds,
      def_files,
      def_id_spans,
      exports,
      module_namespace_defs: Arc::new(self.module_namespace_defs.clone()),
      namespace_members,
      qualified_def_members: Arc::clone(&self.qualified_def_members),
      file_registry: Arc::new(self.file_registry.clone()),
      host: Arc::clone(&self.host),
      checker_caches: self.checker_caches.clone(),
      cache_mode: self.compiler_options.cache.mode,
      cache_options: self.compiler_options.cache.clone(),
      jsx_mode: self.compiler_options.jsx,
      query_stats: self.query_stats.clone(),
      cancelled: Arc::clone(&self.cancelled),
    }
  }

  fn file_key_for_id(&self, id: FileId) -> Option<FileKey> {
    self.file_registry.lookup_key(id)
  }

  fn intern_file_key(&mut self, key: FileKey, origin: FileOrigin) -> FileId {
    let id = self.file_registry.intern(&key, origin);
    if matches!(origin, FileOrigin::Lib) {
      self.lib_file_ids.insert(id);
    }
    id
  }

  fn def_namespaces(kind: &DefKind) -> sem_ts::Namespace {
    match kind {
      DefKind::Function(_) | DefKind::Var(_) => sem_ts::Namespace::VALUE,
      DefKind::VarDeclarator(_) => sem_ts::Namespace::empty(),
      DefKind::Class(_) | DefKind::Enum(_) => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
      DefKind::Interface(_) => sem_ts::Namespace::TYPE,
      DefKind::TypeAlias(_) => sem_ts::Namespace::TYPE,
      DefKind::Namespace(_) | DefKind::Module(_) => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
      }
      DefKind::Import(_) | DefKind::ImportAlias(_) => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
      }
    }
  }

  fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(data) = self.def_data.get(&def) else {
      return u8::MAX;
    };
    if !Self::def_namespaces(&data.kind).contains(ns) {
      return u8::MAX;
    }
    if ns.contains(sem_ts::Namespace::VALUE) {
      return match &data.kind {
        DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_) => 0,
        DefKind::Var(var) => {
          let (hir_kind, hir_parent) = self
            .hir_lowered
            .get(&data.file)
            .and_then(|lowered| {
              lowered
                .def(def)
                .map(|hir_def| (hir_def.path.kind, hir_def.parent))
            })
            .unwrap_or((HirDefKind::Unknown, None));
          if matches!(hir_kind, HirDefKind::VarDeclarator) {
            return 6;
          }

          let has_initializer = if matches!(hir_kind, HirDefKind::Var) {
            hir_parent
              .and_then(|parent| {
                self
                  .hir_lowered
                  .get(&data.file)
                  .and_then(|lowered| lowered.def(parent))
              })
              .is_some_and(|parent_def| {
                matches!(parent_def.path.kind, HirDefKind::VarDeclarator)
                  && parent_def.body.is_some()
              })
          } else {
            false
          };

          if has_initializer || var.body != MISSING_BODY {
            1
          } else {
            4
          }
        }
        DefKind::Namespace(_) | DefKind::Module(_) => 2,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 3,
        DefKind::VarDeclarator(_) => u8::MAX,
        DefKind::Interface(_) | DefKind::TypeAlias(_) => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::TYPE) {
      return match &data.kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        DefKind::Class(_) => 2,
        DefKind::Enum(_) => 3,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 4,
        DefKind::VarDeclarator(_) => 5,
        _ => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::NAMESPACE) {
      return match &data.kind {
        DefKind::Namespace(_) | DefKind::Module(_) => 0,
        DefKind::Import(_) | DefKind::ImportAlias(_) => 1,
        DefKind::VarDeclarator(_) => 2,
        _ => 2,
      };
    }
    u8::MAX
  }

  pub(crate) fn map_decl_to_program_def(
    &self,
    decl: &sem_ts::DeclData,
    ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let direct = DefId(decl.def_id.0);
    if self.def_data.contains_key(&direct) {
      return Some(direct);
    }

    let mut best: Option<(u8, DefId)> = None;
    for (id, data) in self.def_data.iter() {
      if data.file == FileId(decl.file.0) && data.name == decl.name {
        let pri = self.def_priority(*id, ns);
        best = best
          .map(|(best_pri, best_id)| {
            if pri < best_pri || (pri == best_pri && id < &best_id) {
              (pri, *id)
            } else {
              (best_pri, best_id)
            }
          })
          .or(Some((pri, *id)));
      }
    }
    best.map(|(_, id)| id)
  }

  fn update_typecheck_roots(&mut self, roots: &[FileId]) {
    let mut keys: Vec<FileKey> = roots
      .iter()
      .copied()
      .filter_map(|id| self.file_registry.lookup_key(id))
      .collect();
    keys.sort_unstable_by(|a, b| a.as_str().cmp(b.as_str()));
    keys.dedup();
    self
      .typecheck_db
      .set_roots(Arc::from(keys.into_boxed_slice()));
  }

  fn sync_typecheck_roots(&mut self) {
    let roots = self.root_ids.clone();
    self.update_typecheck_roots(&roots);
  }

  fn filter_skip_lib_check_diagnostics(&self, diagnostics: &mut Vec<Diagnostic>) {
    if !self.compiler_options.skip_lib_check {
      return;
    }

    diagnostics.retain(|diag| {
      if self.file_kinds.get(&diag.primary.file) != Some(&FileKind::Dts) {
        return true;
      }
      let code = diag.code.as_str();
      !code.starts_with("TC") && !code.starts_with("BIND")
    });
  }

  fn program_diagnostics(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<Arc<[Diagnostic]>, FatalError> {
    if self.snapshot_loaded {
      let mut diagnostics = self.diagnostics.clone();
      self.filter_skip_lib_check_diagnostics(&mut diagnostics);
      return Ok(Arc::from(diagnostics));
    }
    self.check_cancelled()?;
    self.ensure_analyzed_result(host, roots)?;
    self.ensure_interned_types(host, roots)?;
    self.body_results.clear();
    self.set_extra_diagnostics_input();

    let body_ids: Vec<_> = {
      let db = self.typecheck_db.clone();
      let mut body_ids: Vec<_> = db::body_to_file(&db)
        .iter()
        .filter_map(|(body, file)| {
          let kind = db::file_kind(&db, *file);
          (!matches!(kind, FileKind::Dts)).then_some(*body)
        })
        .collect();
      body_ids.sort_by_key(|id| id.0);
      body_ids
    };

    let shared_context = self.body_check_context();
    // Parent body results (especially top-level bodies) are needed to seed bindings for many
    // child bodies. Compute these sequentially once and seed each parallel worker with the
    // results to avoid redundant work (and pathological contention) during parallel checking.
    let mut seed_results: Vec<(BodyId, Arc<BodyCheckResult>)> = Vec::new();
    let mut remaining: Vec<BodyId> = Vec::with_capacity(body_ids.len());
    let seed_db = BodyCheckDb::from_shared_context(Arc::clone(&shared_context));
    for body in body_ids.iter().copied() {
      let is_top_level = shared_context
        .body_info
        .get(&body)
        .map(|info| matches!(info.kind, HirBodyKind::TopLevel))
        .unwrap_or(false);
      if is_top_level {
        seed_results.push((body, db::queries::body_check::check_body(&seed_db, body)));
      } else {
        remaining.push(body);
      }
    }
    let seed_cache_stats = seed_db.into_cache_stats();
    let seed_results = Arc::new(seed_results);
    use rayon::prelude::*;
    let (cache_stats, mut results): (CheckerCacheStats, Vec<(BodyId, Arc<BodyCheckResult>)>) =
      remaining
        .par_iter()
        .fold(
          || {
            (
              BodyCheckDb::from_shared_context_with_seed_results(
                Arc::clone(&shared_context),
                seed_results.as_slice(),
              ),
              Vec::new(),
            )
          },
          |(db, mut results), body| {
            results.push((*body, db::queries::body_check::check_body(&db, *body)));
            (db, results)
          },
        )
        .map(|(db, results)| (db.into_cache_stats(), results))
        .reduce(
          || (CheckerCacheStats::default(), Vec::new()),
          |(mut stats, mut merged), (thread_stats, results)| {
            stats.merge(&thread_stats);
            merged.extend(results);
            (stats, merged)
          },
        );
    results.extend(seed_results.iter().map(|(id, res)| (*id, Arc::clone(res))));
    let mut cache_stats = cache_stats;
    cache_stats.merge(&seed_cache_stats);

    // Preserve determinism regardless of parallel scheduling.
    results.sort_by_key(|(id, _)| id.0);
    for (body, res) in results {
      self.body_results.insert(body, Arc::clone(&res));
      self.typecheck_db.set_body_result(body, res);
    }

    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      self.cache_stats.merge(&cache_stats);
    }

    let db = self.typecheck_db.clone();
    let mut diagnostics: Vec<_> = db::program_diagnostics(&db).as_ref().to_vec();
    diagnostics.extend(self.diagnostics.clone());
    let mut seen = HashSet::new();
    diagnostics.retain(|diag| {
      seen.insert((
        diag.code.clone(),
        diag.severity,
        diag.message.clone(),
        diag.primary,
      ))
    });
    codes::normalize_diagnostics(&mut diagnostics);
    self.filter_skip_lib_check_diagnostics(&mut diagnostics);
    Ok(Arc::from(diagnostics))
  }

  fn recompute_global_bindings(&mut self) {
    self.global_bindings = crate::db::global_bindings(self);
  }
  fn ensure_body_map_from_defs(&mut self) {
    for (file, state) in self.files.iter() {
      if let Some(body) = state.top_body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: *file,
          hir: None,
          kind: HirBodyKind::Unknown,
        });
      }
    }
    for data in self.def_data.values() {
      let body = match &data.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) if var.body != MISSING_BODY => Some(var.body),
        DefKind::VarDeclarator(var) => var.body,
        DefKind::Class(class) => class.body,
        DefKind::Enum(en) => en.body,
        DefKind::Namespace(ns) => ns.body,
        DefKind::Module(ns) => ns.body,
        _ => None,
      };
      if let Some(body) = body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: data.file,
          hir: None,
          kind: HirBodyKind::Unknown,
        });
      }
    }
  }

  fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    let binding = self
      .global_bindings
      .iter()
      .find(|(_, binding)| binding.symbol == symbol);

    let resolve_def_type = |def_id: DefId| {
      self
        .interned_def_types
        .get(&def_id)
        .copied()
        .or_else(|| self.def_types.get(&def_id).copied())
    };

    let mut def = self
      .symbol_to_def
      .get(&symbol)
      .copied()
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.def));
    let mut file = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.file));
    let mut span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));
    let mut name = def
      .and_then(|def_id| self.def_data.get(&def_id).map(|data| data.name.clone()))
      .or_else(|| binding.as_ref().map(|(name, _)| name.to_string()));
    let mut type_id = def
      .and_then(resolve_def_type)
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.type_id));

    if def.is_none() {
      if let Some(semantics) = self.semantics.as_ref() {
        let sem_symbol: sem_ts::SymbolId = symbol.into();
        if let Some(sym_data) = semantics.symbols().symbol_opt(sem_symbol) {
          for ns in [
            sem_ts::Namespace::VALUE,
            sem_ts::Namespace::TYPE,
            sem_ts::Namespace::NAMESPACE,
          ] {
            if !sym_data.namespaces.contains(ns) {
              continue;
            }
            if let Some(decl_id) = semantics.symbol_decls(sem_symbol, ns).first() {
              let decl = semantics.symbols().decl(*decl_id);
              def = Some(decl.def_id);
              file = Some(decl.file);
              if name.is_none() {
                name = Some(sym_data.name.clone());
              }
              if type_id.is_none() {
                type_id = resolve_def_type(decl.def_id);
              }
              break;
            }
          }
        }
      }
    }

    if span.is_none() {
      span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));
    }

    if def.is_none() && type_id.is_none() && name.is_none() && file.is_none() {
      if self.snapshot_loaded {
        if let Some(local) = self.local_symbol_info.get(&symbol) {
          return Some(SymbolInfo {
            symbol,
            def: None,
            file: Some(local.file),
            type_id: None,
            name: Some(local.name.clone()),
            span: local.span,
          });
        }
      }
      let mut files: Vec<_> = self.file_kinds.keys().copied().collect();
      files.sort_by_key(|file| file.0);
      for file in files {
        let locals = crate::db::local_symbol_info(&self.typecheck_db, file);
        if let Some(local) = locals.get(&symbol) {
          return Some(SymbolInfo {
            symbol,
            def: None,
            file: Some(local.file),
            type_id: None,
            name: Some(local.name.clone()),
            span: local.span,
          });
        }
      }
      return None;
    }
    if name.is_none() {
      name = binding.as_ref().map(|(name, _)| name.to_string());
    }

    Some(SymbolInfo {
      symbol,
      def,
      file,
      type_id,
      name,
      span,
    })
  }

  fn expr_at(&mut self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    if self.snapshot_loaded {
      if self.body_results.is_empty() {
        return None;
      }

      let mut best_containing: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, ExprId),
        (BodyId, ExprId, TextRange),
      )> = None;
      let mut best_empty: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, ExprId),
        (BodyId, ExprId, TextRange),
      )> = None;

      for (body_id, result) in self.body_results.iter() {
        let Some(meta) = self.body_map.get(body_id) else {
          continue;
        };
        if meta.file != file {
          continue;
        }
        let Some((expr_id, _)) = result.expr_at(offset) else {
          continue;
        };
        let Some(span) = result.expr_span(expr_id) else {
          continue;
        };

        let Some(body_span) = body_extent_from_spans(result.expr_spans(), result.pat_spans())
        else {
          continue;
        };
        let key = (
          span.len(),
          span.start,
          span.end,
          body_span.len(),
          body_span.start,
          body_span.end,
          *body_id,
          expr_id,
        );

        if span.start <= offset && offset < span.end {
          if best_containing
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_containing = Some((key, (*body_id, expr_id, span)));
          }
        } else if span.is_empty() && span.start == offset {
          if best_empty
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_empty = Some((key, (*body_id, expr_id, span)));
          }
        }
      }

      return match (best_containing, best_empty) {
        (
          Some((_, (cont_body, cont_expr, cont_span))),
          Some((_, (empty_body, empty_expr, empty_span))),
        ) => {
          if empty_span.start > cont_span.start && empty_span.end < cont_span.end {
            Some((empty_body, empty_expr))
          } else {
            Some((cont_body, cont_expr))
          }
        }
        (Some((_, (body, expr, _))), None) => Some((body, expr)),
        (None, Some((_, (body, expr, _)))) => Some((body, expr)),
        (None, None) => None,
      };
    }

    db::expr_at(&self.typecheck_db, file, offset)
  }

  fn pat_at(&mut self, file: FileId, offset: u32) -> Option<(BodyId, PatId)> {
    if self.snapshot_loaded {
      let mut best_containing: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, PatId),
        (BodyId, PatId, TextRange),
      )> = None;
      let mut best_empty: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, PatId),
        (BodyId, PatId, TextRange),
      )> = None;

      for (body_id, result) in self.body_results.iter() {
        let Some(meta) = self.body_map.get(body_id) else {
          continue;
        };
        if meta.file != file {
          continue;
        }
        let Some((pat_id, span)) = expr_at_from_spans(result.pat_spans(), offset) else {
          continue;
        };
        let pat_id = PatId(pat_id.0);
        let Some(body_span) = body_extent_from_spans(result.expr_spans(), result.pat_spans())
        else {
          continue;
        };
        let key = (
          span.len(),
          span.start,
          span.end,
          body_span.len(),
          body_span.start,
          body_span.end,
          *body_id,
          pat_id,
        );

        if span.start <= offset && offset < span.end {
          if best_containing
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_containing = Some((key, (*body_id, pat_id, span)));
          }
        } else if span.is_empty() && span.start == offset {
          if best_empty
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_empty = Some((key, (*body_id, pat_id, span)));
          }
        }
      }

      match (best_containing, best_empty) {
        (
          Some((_, (cont_body, cont_pat, cont_span))),
          Some((_, (empty_body, empty_pat, empty_span))),
        ) => {
          if empty_span.start > cont_span.start && empty_span.end < cont_span.end {
            return Some((empty_body, empty_pat));
          }
          return Some((cont_body, cont_pat));
        }
        (Some((_, (body, pat, _))), None) => return Some((body, pat)),
        (None, Some((_, (body, pat, _)))) => return Some((body, pat)),
        (None, None) => return None,
      }
    }

    db::file_span_index(&self.typecheck_db, file)
      .pat_at(offset)
      .map(|res| res.id)
  }

  fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    self.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => {
        if var.body != MISSING_BODY {
          Some(var.body)
        } else {
          self.var_initializer(def).map(|init| init.body)
        }
      }
      DefKind::VarDeclarator(var) => var.body,
      DefKind::Class(class) => class.body,
      DefKind::Enum(en) => en.body,
      DefKind::Namespace(ns) => ns.body,
      DefKind::Module(ns) => ns.body,
      DefKind::Import(_) | DefKind::ImportAlias(_) => None,
      DefKind::Interface(_) => None,
      DefKind::TypeAlias(_) => None,
    })
  }

  fn owner_of_body(&self, body: BodyId) -> Option<DefId> {
    self.body_owners.get(&body).copied()
  }

  fn alloc_def(&mut self) -> DefId {
    let id = DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn alloc_symbol(&mut self) -> semantic_js::SymbolId {
    let id = semantic_js::SymbolId(self.next_symbol.into());
    self.next_symbol += 1;
    id
  }

  fn extend_symbol_to_def_with_semantic_ids(&mut self) {
    let Some(semantics) = self.semantics.as_deref() else {
      return;
    };

    let mut defs: Vec<DefId> = self.def_data.keys().copied().collect();
    defs.sort_by_key(|def| def.0);

    let mut symbols: Vec<sem_ts::SymbolId> = Vec::new();
    for def in defs {
      for ns in [
        sem_ts::Namespace::VALUE,
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
      ] {
        if let Some(symbol) = semantics.symbol_for_def(def, ns) {
          symbols.push(symbol);
        }
      }
    }
    symbols.sort_by_key(|symbol| symbol.0);
    symbols.dedup();

    for symbol in symbols {
      let data = semantics.symbols().symbol(symbol);
      let mut canonical_def = None;
      for ns in [
        sem_ts::Namespace::VALUE,
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
      ] {
        if !data.namespaces.contains(ns) {
          continue;
        }
        if let Some(decl_id) = semantics.symbol_decls(symbol, ns).first() {
          canonical_def = Some(semantics.symbols().decl(*decl_id).def_id);
          break;
        }
      }

      if let Some(def) = canonical_def {
        self.symbol_to_def.entry(symbol.into()).or_insert(def);
      }
    }
  }

  fn record_def_symbol(&mut self, def: DefId, symbol: semantic_js::SymbolId) {
    self.symbol_to_def.insert(symbol, def);
  }

  fn record_symbol(&mut self, file: FileId, range: TextRange, symbol: semantic_js::SymbolId) {
    self
      .symbol_occurrences
      .entry(file)
      .or_default()
      .push(SymbolOccurrence { range, symbol });
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn initializer_bodies_have_function_parent() {
    let source = r#"
function Box() {}

function onlyObjects(val: object | number) {
  if (val instanceof Box) {
    const inner = val;
    return inner;
  }
  return val;
}
"#;

    let mut host = crate::MemoryHost::new();
    let file_key = FileKey::new("main.ts");
    host.insert(file_key.clone(), source);
    let program = Program::new(host, vec![file_key.clone()]);
    let _ = program.check();
    let file_id = program.file_id(&file_key).expect("file id");

    let state = program.lock_state();
    let only_objects_def = state
      .def_data
      .iter()
      .find_map(|(def, data)| {
        (data.file == file_id
          && data.name == "onlyObjects"
          && matches!(data.kind, DefKind::Function(_)))
        .then_some(*def)
      })
      .expect("onlyObjects def");
    let only_objects_body = match state.def_data.get(&only_objects_def).map(|d| &d.kind) {
      Some(DefKind::Function(func)) => func.body.expect("onlyObjects body"),
      other => panic!("unexpected def kind for onlyObjects: {other:?}"),
    };

    let inner_initializer_body = state
      .def_data
      .iter()
      .find_map(|(def, data)| {
        (data.file == file_id && data.name == "inner")
          .then(|| state.body_of_def(*def))
          .flatten()
      })
      .expect("inner body");

    let inner_meta = state
      .body_map
      .get(&inner_initializer_body)
      .expect("inner meta");
    assert_eq!(inner_meta.kind, HirBodyKind::Initializer);

    let parent = state
      .body_parents
      .get(&inner_initializer_body)
      .copied()
      .expect("initializer body parent");
    assert_eq!(
      parent, only_objects_body,
      "expected initializer body parent to be enclosing function body"
    );
    let parent_kind = state.body_map.get(&parent).map(|m| m.kind);
    assert_eq!(parent_kind, Some(HirBodyKind::Function));
  }

  #[test]
  fn narrowing_patterns_fixture_initializer_parent_chain() {
    let source = include_str!("../../tests/litmus/narrowing_patterns/main.ts");
    let mut host = crate::MemoryHost::new();
    let file_key = FileKey::new("main.ts");
    host.insert(file_key.clone(), source);
    let program = Program::new(host, vec![file_key.clone()]);
    let _ = program.check();
    let file_id = program.file_id(&file_key).expect("file id");

    let mut state = program.lock_state();
    let only_objects_def = state
      .def_data
      .iter()
      .find_map(|(def, data)| {
        (data.file == file_id
          && data.name == "onlyObjects"
          && matches!(data.kind, DefKind::Function(_)))
        .then_some(*def)
      })
      .expect("onlyObjects def");
    let only_objects_body = match state.def_data.get(&only_objects_def).map(|d| &d.kind) {
      Some(DefKind::Function(func)) => func.body.expect("onlyObjects body"),
      other => panic!("unexpected def kind for onlyObjects: {other:?}"),
    };

    let inner_initializer_body = state
      .def_data
      .iter()
      .find_map(|(def, data)| {
        (data.file == file_id && data.name == "inner")
          .then(|| state.body_of_def(*def))
          .flatten()
      })
      .expect("inner body");
    let inner_meta = state
      .body_map
      .get(&inner_initializer_body)
      .expect("inner meta");
    assert_eq!(inner_meta.kind, HirBodyKind::Initializer);

    let parent = state
      .body_parents
      .get(&inner_initializer_body)
      .copied()
      .expect("initializer body parent");
    assert_eq!(
      parent, only_objects_body,
      "expected narrowing_patterns inner initializer body to be parented to onlyObjects body"
    );

    let lowered = state.hir_lowered.get(&file_id).expect("lowered");
    let only_objects_hir = lowered
      .body(only_objects_body)
      .expect("onlyObjects hir body");
    let val_pat_id = only_objects_hir
      .function
      .as_ref()
      .and_then(|func| func.params.first())
      .map(|param| param.pat)
      .expect("val param pat");
    let val_pat = only_objects_hir
      .pats
      .get(val_pat_id.0 as usize)
      .expect("val pat");
    let val_name = match &val_pat.kind {
      HirPatKind::Ident(name_id) => lowered.names.resolve(*name_id),
      _ => None,
    };
    assert_eq!(val_name, Some("val"));

    let only_objects_result = state
      .check_body(only_objects_body)
      .expect("check onlyObjects");
    let val_pat_ty = only_objects_result
      .pat_type(PatId(val_pat_id.0))
      .expect("val pat type");
    assert_ne!(val_pat_ty, state.interned_unknown());

    // Ensure no body in this fixture reports `val` as an unknown identifier.
    let mut bodies: Vec<_> = state
      .body_map
      .iter()
      .filter_map(|(body, meta)| (meta.file == file_id).then_some((*body, meta.kind)))
      .collect();
    bodies.sort_by_key(|(id, _)| id.0);
    for (body, kind) in bodies {
      let result = state.check_body(body).expect("check body");
      if let Some(diag) = result
        .diagnostics
        .iter()
        .find(|diag| diag.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str())
      {
        let owner = state.owner_of_body(body);
        let owner_name = owner
          .and_then(|id| state.def_data.get(&id).map(|data| data.name.clone()))
          .unwrap_or_else(|| "<unknown>".to_string());
        panic!(
          "unexpected unknown identifier diagnostic in body {:?} ({:?}) owner {:?} `{}`: {:?}",
          body, kind, owner, owner_name, diag
        );
      }
    }
  }
}

fn type_member_name(key: &TypePropertyKey) -> Option<String> {
  match key {
    TypePropertyKey::Identifier(name) => Some(name.clone()),
    TypePropertyKey::String(name) => Some(name.clone()),
    TypePropertyKey::Number(name) => Some(name.clone()),
    TypePropertyKey::Computed(_) => None,
  }
}

fn fatal_to_diagnostic(fatal: FatalError) -> Diagnostic {
  let placeholder = Span::new(FileId(0), TextRange::new(0, 0));
  match fatal {
    FatalError::Host(err) => {
      let mut diagnostic = codes::HOST_ERROR.error(err.to_string(), placeholder);
      diagnostic.push_note("no source span available for this host error; input may be missing");
      diagnostic
    }
    FatalError::Cancelled => codes::CANCELLED.error("operation cancelled", placeholder),
    FatalError::Ice(ice) => {
      let span = span_from_context(&ice.context, placeholder);
      let mut diagnostic = codes::INTERNAL_COMPILER_ERROR
        .error(format!("internal compiler error: {}", ice.message), span);
      if let Some(backtrace) = ice.backtrace {
        diagnostic.push_note(backtrace);
      }
      diagnostic
    }
    FatalError::OutOfMemory => codes::OUT_OF_MEMORY.error("out of memory", placeholder),
  }
}

fn span_from_context(ctx: &IceContext, placeholder: Span) -> Span {
  ctx
    .file
    .map(|file| Span::new(file, TextRange::new(0, 0)))
    .unwrap_or(placeholder)
}

fn loc_to_span(file: FileId, loc: Loc) -> Span {
  Span {
    file,
    range: TextRange {
      start: loc.0.min(u32::MAX as usize) as u32,
      end: loc.1.min(u32::MAX as usize) as u32,
    },
  }
}
