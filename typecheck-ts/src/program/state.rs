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
mod interned;
mod module_exports;

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
  interned_revision: Option<salsa::Revision>,
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
      interned_revision: None,
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
    self.interned_revision = None;
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

  fn canonical_defs(
    &mut self,
  ) -> Result<HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId>, FatalError> {
    self.check_cancelled()?;
    let mut parent_by_def: HashMap<DefId, Option<DefId>> = HashMap::new();
    let mut lowered_entries: Vec<_> = self
      .hir_lowered
      .iter()
      .map(|(file, lowered)| (*file, lowered.clone()))
      .collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);
    for (_file, lowered) in lowered_entries.iter() {
      self.check_cancelled()?;
      for def in lowered.defs.iter() {
        parent_by_def.insert(def.id, def.parent);
      }
    }

    let mut def_entries: Vec<(DefId, DefData)> = Vec::with_capacity(self.def_data.len());
    for (idx, (id, data)) in self.def_data.iter().enumerate() {
      if (idx % 2048) == 0 {
        self.check_cancelled()?;
      }
      def_entries.push((*id, data.clone()));
    }
    self.check_cancelled()?;
    def_entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
    let mut def_by_name: HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId> =
      HashMap::new();
    for (idx, (def_id, data)) in def_entries.into_iter().enumerate() {
      if (idx % 256) == 0 {
        self.check_cancelled()?;
      }
      let namespaces = Self::def_namespaces(&data.kind);
      let parent = parent_by_def.get(&def_id).copied().flatten();
      for ns in [
        sem_ts::Namespace::VALUE,
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
      ] {
        if !namespaces.contains(ns) {
          continue;
        }
        if (idx % 256) == 0 {
          self.check_cancelled()?;
        }
        let key = (data.file, parent, data.name.clone(), ns);
        let mut mapped_def = def_id;
        if let DefKind::Import(import) = &data.kind {
          self.check_cancelled()?;
          if let Some(target) = self
            .exports_for_import(import)?
            .get(&import.original)
            .and_then(|entry| entry.def)
          {
            mapped_def = target;
          }
        }
        match def_by_name.entry(key) {
          std::collections::hash_map::Entry::Vacant(slot) => {
            slot.insert(mapped_def);
          }
          std::collections::hash_map::Entry::Occupied(mut slot) => {
            let existing = slot.get_mut();
            let current = self.def_priority(*existing, ns);
            let new_pri = self.def_priority(mapped_def, ns);
            if new_pri < current || (new_pri == current && mapped_def < *existing) {
              *existing = mapped_def;
            }
          }
        }
      }
    }

    // TypeScript's global declarations merge across `.d.ts` files. The semantic
    // binder already performs this merge when populating `global_symbols`, but
    // the checker-side canonical map is keyed by `(file, parent, name, ns)`.
    //
    // When we vendor the full upstream `lib.*.d.ts` set, important interfaces
    // like `Promise` and `SymbolConstructor` are declared/augmented across many
    // files. Map every top-level global declaration that participates in a
    // merged global symbol group to a single canonical `DefId` so that
    // `ensure_interned_types` can merge their shapes.
    if let Some(sem) = self.semantics.as_deref() {
      let symbols = sem.symbols();
      for (_global_name, group) in sem.global_symbols().iter() {
        for ns in [
          sem_ts::Namespace::VALUE,
          sem_ts::Namespace::TYPE,
          sem_ts::Namespace::NAMESPACE,
        ] {
          let Some(symbol) = group.symbol_for(ns, symbols) else {
            continue;
          };
          let decls = sem.symbol_decls(symbol, ns);
          if decls.is_empty() {
            continue;
          }

          // Only consider top-level declarations here; nested `declare global`
          // blocks currently use distinct parents and are handled elsewhere.
          let mut best: Option<(u8, DefId)> = None;
          let mut top_level_decls = Vec::new();
          for decl in decls.iter().copied() {
            let decl_data = symbols.decl(decl);
            let def = decl_data.def_id;
            let parent = parent_by_def.get(&def).copied().flatten();
            if parent.is_some() {
              continue;
            }
            top_level_decls.push(decl_data);
            let pri = self.def_priority(def, ns);
            best = best
              .map(|(best_pri, best_id)| {
                if pri < best_pri || (pri == best_pri && def < best_id) {
                  (pri, def)
                } else {
                  (best_pri, best_id)
                }
              })
              .or(Some((pri, def)));
          }

          let Some((_, canonical)) = best else {
            continue;
          };

          for decl_data in top_level_decls {
            let key = (decl_data.file, None, decl_data.name.clone(), ns);
            if let Some(slot) = def_by_name.get_mut(&key) {
              *slot = canonical;
            }
          }
        }
      }
    }
    Ok(def_by_name)
  }

  fn rebuild_namespace_member_index(&mut self) -> Result<(), FatalError> {
    let mut index = NamespaceMemberIndex::default();
    let mut lowered_entries: Vec<_> = self.hir_lowered.iter().collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);

    let namespaces_for_hir_kind = |kind: HirDefKind| -> sem_ts::Namespace {
      match kind {
        HirDefKind::Class | HirDefKind::Enum => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Interface | HirDefKind::TypeAlias => sem_ts::Namespace::TYPE,
        HirDefKind::Namespace | HirDefKind::Module => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
        }
        HirDefKind::ImportBinding => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
        }
        _ => sem_ts::Namespace::VALUE,
      }
    };

    for (file_idx, (_file, lowered)) in lowered_entries.into_iter().enumerate() {
      if (file_idx % 16) == 0 {
        self.check_cancelled()?;
      }
      for (idx, def) in lowered.defs.iter().enumerate() {
        if (idx % 4096) == 0 {
          self.check_cancelled()?;
        }
        let Some(parent) = def.parent else {
          continue;
        };
        let Some(name) = lowered.names.resolve(def.name) else {
          continue;
        };
        let name = name.to_string();
        let namespaces = namespaces_for_hir_kind(def.path.kind);
        for ns in [
          sem_ts::Namespace::VALUE,
          sem_ts::Namespace::TYPE,
          sem_ts::Namespace::NAMESPACE,
        ] {
          if !namespaces.contains(ns) {
            continue;
          }
          let mut member_def = def.id;
          if ns.contains(sem_ts::Namespace::VALUE)
            && matches!(def.path.kind, HirDefKind::Class | HirDefKind::Enum)
          {
            if let Some(value_def) = self.value_defs.get(&def.id).copied() {
              member_def = value_def;
            }
          }
          index.insert(parent, ns, name.clone(), member_def);
        }
      }
    }

    index.finalize();
    self.namespace_member_index = Some(Arc::new(index));
    Ok(())
  }

  fn rebuild_callable_overloads(&mut self) {
    self.callable_overloads.clear();
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      let mut seen_symbols = HashSet::new();
      for def_id in self
        .def_data
        .iter()
        .filter_map(|(def_id, data)| matches!(data.kind, DefKind::Function(_)).then_some(def_id))
      {
        let Some(symbol) =
          semantics.symbol_for_def(sem_ts::DefId(def_id.0), sem_ts::Namespace::VALUE)
        else {
          continue;
        };
        if !seen_symbols.insert(symbol) {
          continue;
        }
        let mut defs = Vec::new();
        let mut seen_defs = HashSet::new();
        for decl_id in semantics.symbol_decls(symbol, sem_ts::Namespace::VALUE) {
          let decl = symbols.decl(*decl_id);
          if !matches!(decl.kind, sem_ts::DeclKind::Function) {
            continue;
          }
          if let Some(mapped) = self.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE) {
            if seen_defs.insert(mapped) {
              defs.push(mapped);
            }
          }
        }
        if !defs.is_empty() {
          for def in defs.iter().copied() {
            if let Some(def_data) = self.def_data.get(&def) {
              self
                .callable_overloads
                .entry((def_data.file, def_data.name.clone()))
                .or_insert_with(|| defs.clone());
            }
          }
        }
      }
    }

    let mut grouped: BTreeMap<(FileId, String), Vec<(DefId, TextRange)>> = BTreeMap::new();
    for (id, data) in self
      .def_data
      .iter()
      .filter(|(_, data)| matches!(data.kind, DefKind::Function(_)))
    {
      grouped
        .entry((data.file, data.name.clone()))
        .or_default()
        .push((*id, data.span));
    }
    for ((file, name), mut defs) in grouped.into_iter() {
      defs.sort_by_key(|(id, span)| (span.start, span.end, id.0));
      let mut ordered: Vec<_> = defs.into_iter().map(|(id, _)| id).collect();
      let key = (file, name.clone());
      if let Some(existing) = self.callable_overloads.get(&key).cloned() {
        ordered.extend(existing);
      }
      ordered.sort_by_key(|id| {
        let span = self
          .def_data
          .get(id)
          .map(|data| data.span)
          .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
        (span.start, span.end, id.0)
      });
      ordered.dedup();
      self.callable_overloads.insert(key, ordered);
    }
  }

  fn callable_overload_defs(&mut self, def: DefId) -> Option<Vec<DefId>> {
    let (file, name) = {
      let data = self.def_data.get(&def)?;
      if !matches!(data.kind, DefKind::Function(_)) {
        return None;
      }
      (data.file, data.name.clone())
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let key = (file, name);
    Some(
      self
        .callable_overloads
        .get(&key)
        .cloned()
        .unwrap_or_else(|| vec![def]),
    )
  }

  fn merged_overload_callable_type(
    &mut self,
    defs: &[DefId],
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    if defs.is_empty() {
      return None;
    }
    let has_overloads = defs.len() > 1;
    let mut collect = |skip_bodies: bool,
                       state: &mut ProgramState,
                       overloads: &mut Vec<tti::SignatureId>,
                       seen_sigs: &mut HashSet<tti::SignatureId>| {
      for def in defs.iter().copied() {
        if skip_bodies && has_overloads {
          if let Some(def_data) = state.def_data.get(&def) {
            if let DefKind::Function(func) = &def_data.kind {
              if func.body.is_some() && func.return_ann.is_none() {
                continue;
              }
            }
          }
        }
        if !state.interned_def_types.contains_key(&def) {
          let _ = state.type_of_def(def);
        }
        let ty = state.interned_def_types.get(&def).copied().or_else(|| {
          state.def_types.get(&def).copied().map(|store_ty| {
            let mapped = store.canon(convert_type_for_display(store_ty, state, store, cache));
            state.interned_def_types.insert(def, mapped);
            mapped
          })
        });
        let Some(ty) = ty else {
          continue;
        };
        if let tti::TypeKind::Callable { overloads: sigs } = store.type_kind(ty) {
          for sig in sigs.iter().copied() {
            if seen_sigs.insert(sig) {
              overloads.push(sig);
            }
          }
        }
      }
    };
    let mut overloads = Vec::new();
    let mut seen_sigs = HashSet::new();
    collect(true, self, &mut overloads, &mut seen_sigs);
    if overloads.is_empty() && has_overloads {
      collect(false, self, &mut overloads, &mut seen_sigs);
    }
    if overloads.is_empty() {
      return None;
    }
    Some(store.canon(store.intern_type(tti::TypeKind::Callable { overloads })))
  }

  fn callable_overload_type_for_def(
    &mut self,
    def: DefId,
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    let defs = self.callable_overload_defs(def)?;
    if defs.len() < 2 {
      return None;
    }
    let merged = self.merged_overload_callable_type(&defs, store, cache)?;
    for member in defs {
      self.interned_def_types.insert(member, merged);
    }
    Some(merged)
  }

  fn merge_callable_overload_types(&mut self) {
    let Some(store) = self.interned_store.clone() else {
      return;
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let mut cache = HashMap::new();
    let mut keys: Vec<_> = self.callable_overloads.keys().cloned().collect();
    keys.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
    for key in keys.into_iter() {
      let Some(defs) = self.callable_overloads.get(&key).cloned() else {
        continue;
      };
      if defs.len() < 2 {
        continue;
      }
      if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache) {
        for def in defs.into_iter() {
          self.interned_def_types.insert(def, merged);
        }
      }
    }
  }

  fn interned_unknown(&self) -> TypeId {
    self
      .interned_store
      .as_ref()
      .map(|s| s.primitive_ids().unknown)
      .unwrap_or(self.builtin.unknown)
  }

  fn find_namespace_def(&self, file: FileId, name: &str) -> Option<DefId> {
    self
      .def_data
      .iter()
      .find_map(|(id, data)| match &data.kind {
        DefKind::Namespace(_) | DefKind::Module(_) if data.file == file && data.name == name => {
          Some(*id)
        }
        _ => None,
      })
  }

  fn merge_namespace_value_types(&mut self) -> Result<(), FatalError> {
    let Some(store) = self.interned_store.clone() else {
      return Ok(());
    };
    fn is_ident_char(byte: u8) -> bool {
      byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$')
    }

    fn find_name_span(source: &str, name: &str, range: TextRange) -> TextRange {
      let bytes = source.as_bytes();
      let start = (range.start as usize).min(bytes.len());
      let end = (range.end as usize).min(bytes.len());
      let slice = &source[start..end];
      let mut offset = 0usize;
      while offset <= slice.len() {
        let Some(pos) = slice[offset..].find(name) else {
          break;
        };
        let abs_start = start + offset + pos;
        let abs_end = abs_start + name.len();
        if abs_end > bytes.len() {
          break;
        }
        let before_ok = abs_start == 0 || !is_ident_char(bytes[abs_start - 1]);
        let after_ok = abs_end == bytes.len() || !is_ident_char(bytes[abs_end]);
        if before_ok && after_ok {
          return TextRange::new(abs_start as u32, abs_end as u32);
        }
        offset = offset.saturating_add(pos.saturating_add(name.len().max(1)));
      }
      range
    }

    let is_top_level = |state: &ProgramState, file: FileId, def: DefId| -> bool {
      let Some(lowered) = state.hir_lowered.get(&file) else {
        return true;
      };
      let Some(hir_def) = lowered.def(def) else {
        return true;
      };
      let mut parent = hir_def.parent;
      while let Some(parent_id) = parent {
        let Some(parent_def) = lowered.def(parent_id) else {
          return false;
        };
        if matches!(parent_def.path.kind, HirDefKind::VarDeclarator) {
          parent = parent_def.parent;
          continue;
        }
        return false;
      }
      true
    };

    let mut entries: Vec<_> = self
      .namespace_object_types
      .iter()
      .map(|(k, v)| (k.clone(), *v))
      .collect();
    entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
    for ((file, name), (ns_interned, ns_store)) in entries.into_iter() {
      let ns_def = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          (data.file == file
            && data.name == name
            && matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
            && is_top_level(self, file, *id))
          .then_some(*id)
        })
        .min_by_key(|id| {
          let span = self
            .def_data
            .get(id)
            .map(|d| d.span)
            .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
          (span.start, span.end, id.0)
        });
      let value_def = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          (data.file == file
            && data.name == name
            && matches!(
              data.kind,
              DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_)
            )
            && is_top_level(self, file, *id))
          .then_some(*id)
        })
        .min_by_key(|id| {
          let span = self
            .def_data
            .get(id)
            .map(|d| d.span)
            .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
          (span.start, span.end, id.0)
        });

      if let (Some(ns_def), Some(val_def)) = (ns_def, value_def) {
        let Some((ns_span, ns_export)) = self
          .def_data
          .get(&ns_def)
          .map(|data| (data.span, data.export))
        else {
          continue;
        };
        let Some((val_span, val_export)) = self
          .def_data
          .get(&val_def)
          .map(|data| (data.span, data.export))
        else {
          continue;
        };

        let file_text = db::file_text(&self.typecheck_db, file);
        let namespace_name_span = find_name_span(file_text.as_ref(), &name, ns_span);
        let value_name_span = find_name_span(file_text.as_ref(), &name, val_span);

        let mut has_error = false;
        if ns_export != val_export {
          has_error = true;
          self.push_program_diagnostic(codes::MERGED_DECLARATIONS_EXPORT_MISMATCH.error(
            format!(
              "Individual declarations in merged declaration '{name}' must be all exported or all local."
            ),
            Span::new(file, namespace_name_span),
          ));
          self.push_program_diagnostic(codes::MERGED_DECLARATIONS_EXPORT_MISMATCH.error(
            format!(
              "Individual declarations in merged declaration '{name}' must be all exported or all local."
            ),
            Span::new(file, value_name_span),
          ));
        }

        if ns_span.start < val_span.start {
          has_error = true;
          self.push_program_diagnostic(codes::NAMESPACE_BEFORE_MERGE_TARGET.error(
            "A namespace declaration cannot be located prior to a class or function with which it is merged.",
            Span::new(file, namespace_name_span),
          ));
        }

        if has_error {
          continue;
        }

        let mut val_interned = self
          .def_types
          .get(&val_def)
          .copied()
          .and_then(|val_store_ty| {
            let mut cache = HashMap::new();
            Some(store.canon(convert_type_for_display(
              val_store_ty,
              self,
              &store,
              &mut cache,
            )))
          })
          .or_else(|| self.interned_def_types.get(&val_def).copied());
        if val_interned
          .map(|ty| {
            matches!(
              store.type_kind(ty),
              tti::TypeKind::Any | tti::TypeKind::Unknown
            )
          })
          .unwrap_or(false)
        {
          val_interned = self.interned_def_types.get(&val_def).copied();
        }
        if let Some(val_ty_interned) = val_interned {
          let merged = store.intersection(vec![val_ty_interned, ns_interned]);
          self.interned_def_types.insert(ns_def, merged);
          self.interned_def_types.insert(val_def, merged);
        }
        if let Some(val_ty) = self.def_types.get(&val_def).copied() {
          self.def_types.insert(ns_def, ns_store);
          self.def_types.insert(val_def, val_ty);
        }
      }
    }
    Ok(())
  }

  fn rebuild_interned_named_def_types(&mut self) {
    self.interned_named_def_types.clear();
    let Some(store) = self.interned_store.as_ref() else {
      return;
    };
    let def_sort_key =
      |def: DefId, data: &DefData| (data.file.0, data.span.start, data.span.end, def.0);
    let mut entries: Vec<(tti::TypeId, (u32, u32, u32, u64), DefId)> = Vec::new();
    for (def, ty) in self.interned_def_types.iter() {
      let Some(data) = self.def_data.get(def) else {
        continue;
      };
      if !matches!(
        data.kind,
        DefKind::Interface(_) | DefKind::TypeAlias(_) | DefKind::Class(_) | DefKind::Enum(_)
      ) {
        continue;
      }
      let ty = store.canon(*ty);
      if matches!(
        store.type_kind(ty),
        tti::TypeKind::Unknown | tti::TypeKind::Any | tti::TypeKind::Never
      ) {
        continue;
      }
      entries.push((ty, def_sort_key(*def, data), *def));
    }
    entries.sort_by(|a, b| (a.0 .0, a.1).cmp(&(b.0 .0, b.1)));
    for (ty, _key, def) in entries.into_iter() {
      self.interned_named_def_types.entry(ty).or_insert(def);
    }
  }

  fn collect_function_decl_types(
    &mut self,
    store: &Arc<tti::TypeStore>,
    def_by_name: &HashMap<(FileId, String), DefId>,
    def_types: &mut HashMap<DefId, tti::TypeId>,
    type_params: &mut HashMap<DefId, Vec<TypeParamId>>,
  ) {
    if self.asts.is_empty() {
      return;
    }
    let resolver_defs = Arc::new(def_by_name.clone());
    let mut def_by_span: HashMap<(FileId, TextRange), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(FileId, String), Vec<DefId>> = HashMap::new();
    for (def_id, data) in self.def_data.iter() {
      if !matches!(data.kind, DefKind::Function(_)) {
        continue;
      }
      def_by_span.insert((data.file, data.span), *def_id);
      defs_by_name
        .entry((data.file, data.name.clone()))
        .or_default()
        .push(*def_id);
    }

    let mut ast_entries: Vec<_> = self
      .asts
      .iter()
      .map(|(file, ast)| (*file, Arc::clone(ast)))
      .collect();
    ast_entries.sort_by_key(|(file, _)| file.0);
    let mut sigs_by_name: HashMap<(FileId, String), Vec<(tti::SignatureId, bool)>> = HashMap::new();
    let mut def_type_params: HashMap<DefId, Vec<TypeParamId>> = HashMap::new();
    for (file, ast) in ast_entries.into_iter() {
      let resolver = Arc::new(DeclTypeResolver::new(
        file,
        Arc::clone(&resolver_defs),
        Arc::clone(&self.qualified_def_members),
      ));
      for stmt in ast.stx.body.iter() {
        let Stmt::FunctionDecl(func) = stmt.stx.as_ref() else {
          continue;
        };
        let span = loc_to_span(file, stmt.loc).range;
        let Some(def_id) = def_by_span.get(&(file, span)).copied() else {
          continue;
        };
        let Some(name) = func.stx.name.as_ref() else {
          continue;
        };
        let has_body = func.stx.function.stx.body.is_some();
        let (sig_id, params, diags) = Self::lower_function_signature(
          store,
          file,
          func.stx.as_ref(),
          Some(resolver.clone()),
          self.compiler_options.no_implicit_any,
        );
        if !diags.is_empty() {
          for diag in diags {
            self.push_program_diagnostic(diag);
          }
        }
        sigs_by_name
          .entry((file, name.stx.name.clone()))
          .or_default()
          .push((sig_id, has_body));
        if !params.is_empty() {
          def_type_params.entry(def_id).or_insert(params);
        }
      }
    }

    for ((file, name), mut sigs) in sigs_by_name.into_iter() {
      let has_overloads = sigs.len() > 1;
      if has_overloads {
        sigs.retain(|(_, has_body)| !*has_body);
      }
      if sigs.is_empty() {
        continue;
      }
      let mut sig_ids: Vec<_> = sigs.into_iter().map(|(id, _)| id).collect();
      sig_ids.sort();
      sig_ids.dedup();
      let callable = store.intern_type(tti::TypeKind::Callable { overloads: sig_ids });
      if let Some(def_ids) = defs_by_name.get(&(file, name)) {
        let shared_params = def_ids
          .iter()
          .find_map(|id| def_type_params.get(id).cloned());
        for def_id in def_ids {
          def_types
            .entry(*def_id)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(store, *existing, callable);
            })
            .or_insert(callable);
          if let Some(params) = def_type_params
            .get(def_id)
            .cloned()
            .or_else(|| shared_params.clone())
          {
            type_params.entry(*def_id).or_insert(params);
          }
        }
      }
    }
  }

  fn check_class_implements(
    &mut self,
    host: &Arc<dyn Host>,
    store: &Arc<tti::TypeStore>,
    def_types: &HashMap<DefId, tti::TypeId>,
    type_params: &HashMap<DefId, Vec<TypeParamId>>,
    type_param_decls: &HashMap<DefId, Arc<[tti::TypeParamDecl]>>,
    lowered_entries: &[(FileId, Arc<LowerResult>)],
    hir_def_maps: &HashMap<FileId, HashMap<HirDefId, DefId>>,
    def_by_name: &HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId>,
  ) -> Result<(), FatalError> {
    if lowered_entries.is_empty() {
      return Ok(());
    }

    let mut ordered_globals: Vec<(String, FileId, DefId)> = def_by_name
      .iter()
      .filter_map(|((file, parent, name, ns), def)| {
        (parent.is_none() && *ns == sem_ts::Namespace::TYPE).then_some((name.clone(), *file, *def))
      })
      .collect();
    ordered_globals.sort_by(|(name_a, file_a, def_a), (name_b, file_b, def_b)| {
      (name_a.as_str(), file_a.0, def_a.0).cmp(&(name_b.as_str(), file_b.0, def_b.0))
    });
    let mut global_types_by_name: HashMap<String, DefId> = HashMap::new();
    for (name, _file, def) in ordered_globals.into_iter() {
      global_types_by_name.entry(name).or_insert(def);
    }

    let caches = self.checker_caches.for_body();
    let expander = RefExpander::new(
      Arc::clone(store),
      def_types,
      type_params,
      type_param_decls,
      &self.interned_intrinsics,
      &self.interned_class_instances,
      caches.eval.clone(),
    );
    let mut hooks = relate_hooks();
    hooks.expander = Some(&expander);
    let relate = RelateCtx::with_hooks_and_cache(
      Arc::clone(store),
      store.options(),
      hooks,
      caches.relation.clone(),
    );
    let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());

    fn resolve_member_symbol<'a>(
      names: &'a hir_js::NameInterner,
      name: &hir_js::PropertyName,
    ) -> Option<&'a str> {
      match name {
        hir_js::PropertyName::Symbol(id) => names.resolve(*id),
        _ => None,
      }
    }

    fn member_span_for_symbol(
      names: &hir_js::NameInterner,
      members: &[hir_js::ClassMemberSig],
      symbol: &str,
    ) -> Option<TextRange> {
      for member in members {
        if member.static_ {
          continue;
        }
        let name = match &member.kind {
          hir_js::ClassMemberSigKind::Field { name, .. } => name,
          hir_js::ClassMemberSigKind::Method { name, .. } => name,
          hir_js::ClassMemberSigKind::Getter { name, .. } => name,
          hir_js::ClassMemberSigKind::Setter { name, .. } => name,
          _ => continue,
        };
        if resolve_member_symbol(names, name) == Some(symbol) {
          return Some(member.span);
        }
      }
      None
    }

    fn find_symbol_key_range(text: &str, span: TextRange, symbol: &str) -> Option<TextRange> {
      let start = span.start as usize;
      let end = span.end as usize;
      let slice = text.get(start..end)?;
      let direct = format!("[Symbol.{symbol}]");
      if let Some(offset) = slice.find(&direct) {
        let start = span.start.saturating_add(offset as u32);
        let end = start.saturating_add(direct.len() as u32);
        return Some(TextRange::new(start, end));
      }
      let computed = format!("[Symbol[\"{symbol}\"]]");
      if let Some(offset) = slice.find(&computed) {
        let start = span.start.saturating_add(offset as u32);
        let end = start.saturating_add(computed.len() as u32);
        return Some(TextRange::new(start, end));
      }
      None
    }

    for (file_idx, (file, lowered)) in lowered_entries.iter().enumerate() {
      if (file_idx % 16) == 0 {
        self.check_cancelled()?;
      }
      if self.compiler_options.skip_lib_check && self.file_kinds.get(file) == Some(&FileKind::Dts) {
        continue;
      }
      let Ok(text) = self.load_text(*file, host) else {
        continue;
      };
      let def_map = hir_def_maps.get(file);
      for def in lowered.defs.iter() {
        let Some(hir_js::DefTypeInfo::Class {
          implements,
          members,
          ..
        }) = def.type_info.as_ref()
        else {
          continue;
        };
        if implements.is_empty() {
          continue;
        }
        let Some(arenas) = lowered.type_arenas(def.id) else {
          continue;
        };
        let mapped = def_map
          .and_then(|map| map.get(&def.id).copied())
          .unwrap_or(def.id);
        let Some(class_ty) = def_types.get(&mapped).copied() else {
          continue;
        };
        for implemented in implements.iter().copied() {
          let mut expr_id = implemented;
          loop {
            let Some(expr) = arenas.type_exprs.get(expr_id.0 as usize) else {
              break;
            };
            match &expr.kind {
              hir_js::TypeExprKind::Parenthesized(inner) => expr_id = *inner,
              _ => break,
            }
          }
          let Some(expr) = arenas.type_exprs.get(expr_id.0 as usize) else {
            continue;
          };
          let hir_js::TypeExprKind::TypeRef(type_ref) = &expr.kind else {
            continue;
          };
          if !type_ref.type_args.is_empty() {
            continue;
          }
          let hir_js::TypeName::Ident(name_id) = &type_ref.name else {
            continue;
          };
          let Some(name) = lowered.names.resolve(*name_id).map(|s| s.to_string()) else {
            continue;
          };
          let def_id = def_by_name
            .get(&(*file, None, name.clone(), sem_ts::Namespace::TYPE))
            .copied()
            .or_else(|| global_types_by_name.get(&name).copied());
          let Some(def_id) = def_id else {
            continue;
          };
          let iface_ty = store.intern_type(tti::TypeKind::Ref {
            def: def_id,
            args: Vec::new(),
          });
          if relate.is_assignable(class_ty, iface_ty) {
            continue;
          }

          let mut mismatched: Option<PropertyKey> = None;
          for prop in queries.properties_of(iface_ty) {
            let Some(actual) = queries.property_type(class_ty, prop.key.clone()) else {
              continue;
            };
            if !relate.is_assignable(actual, prop.ty) {
              mismatched = Some(prop.key);
              break;
            }
          }
          let Some(PropertyKey::Symbol(symbol)) = mismatched else {
            continue;
          };
          let Some(member_span) = member_span_for_symbol(&lowered.names, members, &symbol) else {
            continue;
          };
          let key_span =
            find_symbol_key_range(text.as_ref(), member_span, &symbol).unwrap_or(member_span);
          self
            .diagnostics
            .push(codes::PROPERTY_IN_TYPE_NOT_ASSIGNABLE_TO_BASE.error(
              "property not assignable to base type",
              Span::new(*file, key_span),
            ));
        }
      }
    }

    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      self.cache_stats.merge(&caches.stats());
    }

    Ok(())
  }

  fn lower_function_signature(
    store: &Arc<tti::TypeStore>,
    file: FileId,
    func: &FuncDecl,
    resolver: Option<Arc<dyn TypeResolver>>,
    no_implicit_any: bool,
  ) -> (tti::SignatureId, Vec<TypeParamId>, Vec<Diagnostic>) {
    let mut lowerer = match resolver {
      Some(resolver) => TypeLowerer::with_resolver(Arc::clone(store), resolver),
      None => TypeLowerer::new(Arc::clone(store)),
    };
    lowerer.set_file(file);
    let prim = store.primitive_ids();
    let mut type_param_decls = Vec::new();
    if let Some(params) = func.function.stx.type_parameters.as_ref() {
      type_param_decls = lowerer.register_type_params(params);
    }
    let type_param_ids: Vec<_> = type_param_decls.iter().map(|d| d.id).collect();
    let mut params = Vec::new();
    let mut this_param = None;
    let mut diagnostics = Vec::new();
    for (idx, param) in func.function.stx.parameters.iter().enumerate() {
      let name = match &*param.stx.pattern.stx.pat.stx {
        Pat::Id(id) => Some(id.stx.name.clone()),
        _ => None,
      };
      let is_this = idx == 0 && matches!(name.as_deref(), Some("this"));
      let annotation = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| lowerer.lower_type_expr(ann));
      let mut ty = annotation.unwrap_or(prim.unknown);
      if annotation.is_none() && !is_this && no_implicit_any {
        // Match TypeScript's error-recovery semantics: keep checking by treating
        // the missing annotation as `any` while emitting `--noImplicitAny`.
        ty = prim.any;
        let span = loc_to_span(file, param.stx.pattern.stx.pat.loc);
        diagnostics
          .push(codes::IMPLICIT_ANY.error(codes::implicit_any_message(name.as_deref()), span));
      }
      if idx == 0 && matches!(name.as_deref(), Some("this")) {
        this_param = Some(ty);
        continue;
      }
      params.push(tti::Param {
        name: name.as_deref().map(|name| store.intern_name(name)),
        ty,
        optional: param.stx.optional,
        rest: param.stx.rest,
      });
    }
    let ret = func
      .function
      .stx
      .return_type
      .as_ref()
      .map(|r| lowerer.lower_type_expr(r))
      .unwrap_or(prim.unknown);
    let sig = tti::Signature {
      params,
      ret,
      type_params: type_param_decls,
      this_param,
    };
    let sig_id = store.intern_signature(sig);
    diagnostics.extend(lowerer.take_diagnostics());
    (sig_id, type_param_ids, diagnostics)
  }

  fn merge_namespace_store_types(&mut self, existing: TypeId, incoming: TypeId) -> TypeId {
    match (
      self.type_store.kind(existing).clone(),
      self.type_store.kind(incoming).clone(),
    ) {
      (TypeKind::Object(mut a), TypeKind::Object(b)) => {
        for (name, prop) in b.props.into_iter() {
          a.props.insert(name, prop);
        }
        if a.string_index.is_none() {
          a.string_index = b.string_index;
        }
        if a.number_index.is_none() {
          a.number_index = b.number_index;
        }
        self.type_store.object(a)
      }
      _ => self
        .type_store
        .union(vec![existing, incoming], &self.builtin),
    }
  }

  fn merge_interned_object_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Object(obj_a), tti::TypeKind::Object(obj_b)) => {
        let mut shape = store.shape(store.object(obj_a).shape);
        let other = store.shape(store.object(obj_b).shape);
        let mut merged = Vec::new();
        for prop in shape
          .properties
          .into_iter()
          .chain(other.properties.into_iter())
        {
          if let Some(existing) = merged
            .iter_mut()
            .find(|p: &&mut Property| p.key == prop.key)
          {
            *existing = prop;
          } else {
            merged.push(prop);
          }
        }
        shape.properties = merged;
        shape.call_signatures.extend(other.call_signatures);
        shape
          .construct_signatures
          .extend(other.construct_signatures);
        shape.indexers.extend(other.indexers);
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn merge_callable_with_object(
    store: &Arc<tti::TypeStore>,
    overloads: &[tti::SignatureId],
    object: tti::ObjectId,
    object_ty: tti::TypeId,
  ) -> tti::TypeId {
    let shape = store.shape(store.object(object).shape);
    let mut merged = overloads.to_vec();
    merged.extend(shape.call_signatures.iter().copied());
    let mut seen = HashSet::new();
    merged.retain(|sig| seen.insert(*sig));
    let callable = store.intern_type(tti::TypeKind::Callable { overloads: merged });
    let has_extras = !shape.properties.is_empty()
      || !shape.construct_signatures.is_empty()
      || !shape.indexers.is_empty();
    if has_extras {
      store.intersection(vec![callable, object_ty])
    } else {
      callable
    }
  }

  fn merge_interned_decl_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Callable { overloads: a }, tti::TypeKind::Callable { overloads: b }) => {
        let mut merged = Vec::with_capacity(a.len() + b.len());
        merged.extend(a);
        merged.extend(b.into_iter());
        let mut seen_ids = HashSet::new();
        merged.retain(|sig| seen_ids.insert(*sig));
        let mut unique = Vec::new();
        let mut seen: HashMap<
          (
            Vec<(tti::TypeId, bool, bool)>,
            Vec<tti::TypeParamDecl>,
            Option<tti::TypeId>,
          ),
          (tti::SignatureId, bool, bool),
        > = HashMap::new();
        for id in merged.into_iter() {
          let sig = store.signature(id);
          let key = (
            sig
              .params
              .iter()
              .map(|p| (p.ty, p.optional, p.rest))
              .collect::<Vec<_>>(),
            sig.type_params.clone(),
            sig.this_param,
          );
          let has_names = sig.params.iter().any(|p| p.name.is_some());
          let ret_kind = store.type_kind(sig.ret);
          let ret_unknown = matches!(ret_kind, tti::TypeKind::Unknown | tti::TypeKind::Any);
          if let Some((prev, prev_named, prev_unknown)) = seen.get(&key).copied() {
            let mut replace = false;
            if prev_unknown && !ret_unknown {
              replace = true;
            } else if !prev_named && has_names && prev_unknown == ret_unknown {
              replace = true;
            }
            if replace {
              if let Some(pos) = unique.iter().position(|s| *s == prev) {
                unique[pos] = id;
              }
              seen.insert(key, (id, has_names, ret_unknown));
            }
          } else {
            seen.insert(key.clone(), (id, has_names, ret_unknown));
            unique.push(id);
          }
        }
        store.intern_type(tti::TypeKind::Callable { overloads: unique })
      }
      (tti::TypeKind::Callable { overloads }, tti::TypeKind::Object(obj)) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, incoming)
      }
      (tti::TypeKind::Object(obj), tti::TypeKind::Callable { overloads }) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, existing)
      }
      (tti::TypeKind::Object(_), tti::TypeKind::Object(_)) => {
        ProgramState::merge_interned_object_types(store, existing, incoming)
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn merge_interface_symbol_types(&mut self, def: DefId) -> Result<(), FatalError> {
    let Some(store) = self.interned_store.as_ref() else {
      return Ok(());
    };
    let Some(semantics) = self.semantics.as_ref() else {
      return Ok(());
    };
    let Some(symbol) = semantics.symbol_for_def(def, sem_ts::Namespace::TYPE) else {
      return Ok(());
    };

    let symbols = semantics.symbols();
    let mut interface_defs: Vec<DefId> = semantics
      .symbol_decls(symbol, sem_ts::Namespace::TYPE)
      .iter()
      .filter_map(|decl_id| {
        let decl = symbols.decl(*decl_id);
        if !matches!(decl.kind, sem_ts::DeclKind::Interface) {
          return None;
        }
        self.map_decl_to_program_def(decl, sem_ts::Namespace::TYPE)
      })
      .collect();

    if interface_defs.len() <= 1 {
      return Ok(());
    }

    interface_defs.sort_by(|a, b| {
      let key = |def: &DefId| {
        self.def_data.get(def).map(|data| {
          (
            data.file.0,
            data.span.start,
            data.span.end,
            def.0,
            data.name.as_str(),
          )
        })
      };
      key(a).cmp(&key(b)).then_with(|| a.0.cmp(&b.0))
    });
    interface_defs.dedup();
    if interface_defs.len() <= 1 {
      return Ok(());
    }

    let prim = store.primitive_ids();
    let mut convert_cache = HashMap::new();
    let mut merged: Option<tti::TypeId> = None;
    for iface_def in interface_defs.iter().copied() {
      let mut ty = self
        .interned_def_types
        .get(&iface_def)
        .copied()
        .map(|ty| store.canon(ty));

      if matches!(
        ty.map(|ty| store.type_kind(ty)),
        Some(tti::TypeKind::Unknown)
      ) || ty.is_none()
      {
        ty = self
          .def_data
          .get(&iface_def)
          .and_then(|data| match &data.kind {
            DefKind::Interface(interface) => {
              let interned =
                convert_type_for_display(interface.typ, self, store, &mut convert_cache);
              Some(store.canon(interned))
            }
            _ => None,
          });
      }

      let Some(ty) = ty else {
        continue;
      };
      if matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
        continue;
      }
      merged = Some(match merged {
        Some(existing) => ProgramState::merge_interned_decl_types(store, existing, ty),
        None => ty,
      });
    }
    let merged = store.canon(merged.unwrap_or(prim.unknown));

    let imported = self.import_interned_type(merged);
    let legacy = if merged == prim.unknown {
      imported
    } else if imported == self.builtin.unknown {
      merged
    } else {
      imported
    };

    for iface_def in interface_defs {
      self.interned_def_types.insert(iface_def, merged);
      self.def_types.insert(iface_def, legacy);
      if let Some(data) = self.def_data.get_mut(&iface_def) {
        if let DefKind::Interface(existing) = &mut data.kind {
          if imported != self.builtin.unknown {
            existing.typ = imported;
          }
        }
      }
    }

    Ok(())
  }

  fn merge_interface_symbol_types_all(&mut self) -> Result<(), FatalError> {
    let mut interface_defs: Vec<DefId> = self
      .def_data
      .iter()
      .filter_map(|(id, data)| matches!(data.kind, DefKind::Interface(_)).then_some(*id))
      .collect();
    interface_defs.sort_by_key(|def| def.0);

    let mut seen_symbols: HashSet<sem_ts::SymbolId> = HashSet::new();
    for def in interface_defs {
      let symbol = self
        .semantics
        .as_ref()
        .and_then(|semantics| semantics.symbol_for_def(def, sem_ts::Namespace::TYPE));
      if let Some(symbol) = symbol {
        if seen_symbols.insert(symbol) {
          self.merge_interface_symbol_types(def)?;
        }
      }
    }
    Ok(())
  }

  fn refresh_import_def_types(&mut self) -> Result<(), FatalError> {
    let mut import_defs: Vec<DefId> = self
      .def_data
      .iter()
      .filter_map(|(def, data)| match data.kind {
        DefKind::Import(_) | DefKind::ImportAlias(_) => Some(*def),
        _ => None,
      })
      .collect();
    import_defs.sort_by(|a, b| {
      let key = |def: &DefId| {
        self.def_data.get(def).map(|data| {
          (
            data.file.0,
            data.span.start,
            data.span.end,
            data.name.as_str(),
            def.0,
          )
        })
      };
      key(a).cmp(&key(b)).then_with(|| a.0.cmp(&b.0))
    });
    import_defs.dedup();

    // Import binding definitions cache the resolved export type. Declaration
    // merging (notably interface merging for module augmentations) can update
    // the exported types after these import defs have already been computed.
    // Drop cached import types and recompute so downstream body checking sees
    // the merged surface.
    for def in import_defs.iter().copied() {
      self.def_types.remove(&def);
      self.interned_def_types.remove(&def);
    }
    for def in import_defs.into_iter() {
      self.type_of_def(def)?;
    }
    Ok(())
  }

  fn collect_libraries(
    &mut self,
    host: &dyn Host,
    roots: &[FileKey],
  ) -> Result<Vec<LibFile>, FatalError> {
    let mut options = self
      .compiler_options_override
      .clone()
      .unwrap_or_else(|| host.compiler_options());
    if !options.no_default_lib && options.libs.is_empty() && !roots.is_empty() {
      for key in roots {
        let text = if let Some(text) = self.file_overrides.get(key) {
          Arc::clone(text)
        } else {
          host.file_text(key)?
        };
        if scan_triple_slash_directives(text.as_ref()).no_default_lib {
          options.no_default_lib = true;
          break;
        }
      }
    }

    self.compiler_options = options.clone();
    self.checker_caches = CheckerCaches::new(options.cache.clone());
    self.cache_stats = CheckerCacheStats::default();
    self.typecheck_db.set_compiler_options(options.clone());
    self
      .typecheck_db
      .set_cancellation_flag(self.cancelled.clone());
    let libs = collect_libs(&options, host.lib_files(), &self.lib_manager);
    if libs.is_empty() && options.no_default_lib {
      self.lib_diagnostics.clear();
      return Ok(Vec::new());
    }
    let validated = validate_libs(libs, |lib| {
      self.intern_file_key(lib.key.clone(), FileOrigin::Lib)
    });
    self.lib_diagnostics = validated.diagnostics.clone();

    let mut dts_libs = Vec::new();
    for (lib, file_id) in validated.libs.into_iter() {
      self.file_kinds.insert(file_id, FileKind::Dts);
      dts_libs.push(lib);
    }

    Ok(dts_libs)
  }

  fn process_libs(
    &mut self,
    libs: &[LibFile],
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) -> Result<(), FatalError> {
    let mut pending: VecDeque<LibFile> = libs.iter().cloned().collect();
    while let Some(lib) = pending.pop_front() {
      self.check_cancelled()?;
      let file_id = self.intern_file_key(lib.key.clone(), FileOrigin::Lib);
      if self.lib_texts.contains_key(&file_id) {
        continue;
      }
      self.file_kinds.insert(file_id, FileKind::Dts);
      self.lib_texts.insert(file_id, lib.text.clone());

      let directives = scan_triple_slash_directives(lib.text.as_ref());
      for reference in directives.references.iter() {
        let value = reference.value(lib.text.as_ref());
        if value.is_empty() {
          continue;
        }
        match reference.kind {
          TripleSlashReferenceKind::Lib => {
            if let Some(lib_file) =
              crate::lib_support::lib_env::bundled_lib_file_by_option_name(value)
            {
              let lib_id = self.intern_file_key(lib_file.key.clone(), FileOrigin::Lib);
              if !self.lib_texts.contains_key(&lib_id) {
                pending.push_back(lib_file);
              }
            } else {
              self.push_program_diagnostic(codes::LIB_DEFINITION_FILE_NOT_FOUND.error(
                format!("cannot find lib definition file for \"{value}\""),
                Span::new(file_id, reference.value_range),
              ));
            }
          }
          TripleSlashReferenceKind::Path => {
            let normalized = normalize_reference_path_specifier(value);
            if let Some(target) = self.record_module_resolution(file_id, normalized.as_ref(), host)
            {
              queue.push_back(target);
            } else {
              self.push_program_diagnostic(codes::FILE_NOT_FOUND.error(
                format!("file \"{}\" not found", normalized.as_ref()),
                Span::new(file_id, reference.value_range),
              ));
            }
          }
          TripleSlashReferenceKind::Types => {
            if let Some(target) = self.record_module_resolution(file_id, value, host) {
              queue.push_back(target);
            } else {
              self.push_program_diagnostic(codes::TYPE_DEFINITION_FILE_NOT_FOUND.error(
                format!("cannot find type definition file for \"{value}\""),
                Span::new(file_id, reference.value_range),
              ));
            }
          }
        }
      }

      let parsed = self.parse_via_salsa(file_id, FileKind::Dts, Arc::clone(&lib.text));
      match parsed {
        Ok(ast) => {
          self.check_cancelled()?;
          let (locals, _) = sem_ts::locals::bind_ts_locals_tables(ast.as_ref(), file_id);
          self.local_semantics.insert(file_id, locals);
          self.asts.insert(file_id, Arc::clone(&ast));
          self.queue_type_imports_in_ast(file_id, ast.as_ref(), host, queue);
          let lowered = db::lower_hir(&self.typecheck_db, file_id);
          let Some(lowered) = lowered.lowered else {
            continue;
          };
          self.hir_lowered.insert(file_id, Arc::clone(&lowered));
          let _bound_sem_hir = self.bind_file(file_id, ast.as_ref(), host, queue);
          let _ = self.align_definitions_with_hir(file_id, lowered.as_ref());
          self.map_hir_bodies(file_id, lowered.as_ref());
        }
        Err(err) => {
          let _ = err;
        }
      }
    }
    Ok(())
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

  fn load_text(&self, file: FileId, host: &Arc<dyn Host>) -> Result<Arc<str>, HostError> {
    let Some(key) = self.file_key_for_id(file) else {
      return Err(HostError::new(format!("missing file key for {file:?}")));
    };
    let origin = self
      .file_registry
      .lookup_origin(file)
      .unwrap_or(FileOrigin::Source);
    if matches!(origin, FileOrigin::Lib) {
      if let Some(text) = self.lib_texts.get(&file) {
        return Ok(text.clone());
      }
    }
    if let Some(text) = self.file_overrides.get(&key) {
      return Ok(text.clone());
    }
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    host.file_text(&key)
  }

  fn record_module_resolution(
    &mut self,
    from: FileId,
    specifier: &str,
    host: &Arc<dyn Host>,
  ) -> Option<FileId> {
    let resolved_key = self
      .file_key_for_id(from)
      .and_then(|from_key| host.resolve(&from_key, specifier));
    let mut resolved = resolved_key.as_ref().map(|target_key| {
      // Prefer an already-known file ID when the host resolution points at a
      // library file key. Many hosts provide `.d.ts` libraries via
      // `Host::lib_files()` only (without implementing `file_text` for them),
      // so interning them as `Source` would create a second `FileId` that
      // cannot be loaded.
      self
        .file_id_for_key(target_key)
        .unwrap_or_else(|| self.intern_file_key(target_key.clone(), FileOrigin::Source))
    });
    if let (Some(file), Some(target_key)) = (resolved, resolved_key.as_ref()) {
      if db::Db::file_input(&self.typecheck_db, file).is_none() {
        // Lib file inputs are seeded up-front in `process_libs`. When resolving
        // module specifiers during lib processing we may see dependent lib IDs
        // before their texts are staged, so only auto-seed source files here.
        let origin = self
          .file_registry
          .lookup_origin(file)
          .unwrap_or(FileOrigin::Source);
        if matches!(origin, FileOrigin::Source) {
          let kind = *self
            .file_kinds
            .entry(file)
            .or_insert_with(|| host.file_kind(target_key));
          match self.load_text(file, host) {
            Ok(text) => self.set_salsa_inputs(file, kind, text),
            Err(_) => resolved = None,
          }
        }
      }
    }
    self
      .typecheck_db
      .set_module_resolution_ref(from, specifier, resolved);
    resolved
  }

  fn set_salsa_inputs(&mut self, file: FileId, kind: FileKind, text: Arc<str>) {
    let key = self
      .file_registry
      .lookup_key(file)
      .unwrap_or_else(|| panic!("file {:?} must be interned before setting inputs", file));
    let origin = self
      .file_registry
      .lookup_origin(file)
      .unwrap_or(FileOrigin::Source);
    if let Some(existing) = db::Db::file_input(&self.typecheck_db, file) {
      let existing_key = existing.key(&self.typecheck_db);
      let existing_kind = existing.kind(&self.typecheck_db);
      let existing_text = existing.text(&self.typecheck_db);
      if existing_kind == kind
        && existing_key == key
        && existing_text.as_ref() == text.as_ref()
        && db::Db::file_origin(&self.typecheck_db, file) == Some(origin)
      {
        return;
      }
    }

    self.typecheck_db.set_file(file, key, kind, text, origin);
  }

  fn parse_via_salsa(
    &mut self,
    file: FileId,
    kind: FileKind,
    text: Arc<str>,
  ) -> Result<Arc<Node<TopLevel>>, Diagnostic> {
    self.set_salsa_inputs(file, kind, Arc::clone(&text));
    let result = db::parse(&self.typecheck_db, file);
    match result.ast {
      Some(ast) => Ok(ast),
      None => Err(result.diagnostics.into_iter().next().unwrap_or_else(|| {
        codes::MISSING_BODY.error("missing parsed AST", Span::new(file, TextRange::new(0, 0)))
      })),
    }
  }

  fn recompute_global_bindings(&mut self) {
    self.global_bindings = crate::db::global_bindings(self);
  }
  /// Remap bound definitions to the stable IDs produced by HIR lowering while
  /// preserving existing symbols and cached types.
  ///
  /// The binder allocates definitions sequentially, but HIR uses content-derived
  /// identifiers that stay stable across edits. Re-aligning keeps
  /// `definitions_in_file`, `expr_at`, and `type_of_def` working across repeated
  /// checks and avoids dropping cached type information when files are
  /// re-lowered.
  fn align_definitions_with_hir(
    &mut self,
    file: FileId,
    lowered: &LowerResult,
  ) -> HashMap<DefId, DefId> {
    let is_file_level_binding = |def: &hir_js::DefData| -> bool {
      if def.in_global {
        // `declare global { ... }` members are injected into the program-wide
        // global scope but do not create file/module bindings.
        return false;
      }

      // `hir-js` models variable declarations as a `VarDeclarator` container
      // owning the initializer body plus one or more `Var` children for the
      // bindings. Treat those `Var` defs as top-level when the declarator
      // itself is top-level.
      let mut parent = def.parent;
      while let Some(parent_id) = parent {
        let Some(parent_def) = lowered.def(parent_id) else {
          return false;
        };
        if matches!(parent_def.path.kind, HirDefKind::VarDeclarator) {
          parent = parent_def.parent;
          continue;
        }
        return false;
      }

      matches!(
        def.path.kind,
        HirDefKind::Var
          | HirDefKind::Function
          | HirDefKind::Class
          | HirDefKind::Enum
          | HirDefKind::Namespace
          | HirDefKind::Module
          | HirDefKind::ImportBinding
          | HirDefKind::Interface
          | HirDefKind::TypeAlias
          | HirDefKind::ExportAlias
      )
    };

    let file_def_ids: HashSet<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .map(|(id, _)| *id)
      .collect();
    let mut by_name_kind: HashMap<(String, DefMatchKind), Vec<(DefId, DefData)>> = HashMap::new();
    for (id, data) in self.def_data.iter() {
      if data.file != file {
        continue;
      }
      by_name_kind
        .entry((data.name.clone(), match_kind_from_def(&data.kind)))
        .or_default()
        .push((*id, data.clone()));
    }
    for defs in by_name_kind.values_mut() {
      defs.sort_by_key(|(_, data)| (data.span.start, data.span.end));
    }

    let mut new_def_data: HashMap<DefId, DefData> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file != file)
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    let mut new_def_types: HashMap<DefId, TypeId> = self
      .def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_def_types: HashMap<DefId, tti::TypeId> = self
      .interned_def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_type_params: HashMap<DefId, Vec<TypeParamId>> = self
      .interned_type_params
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, params)| (*id, params.clone()))
      .collect();
    let mut new_interned_type_param_decls: HashMap<DefId, Arc<[tti::TypeParamDecl]>> = self
      .interned_type_param_decls
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, decls)| (*id, Arc::clone(decls)))
      .collect();
    let mut id_mapping: HashMap<DefId, DefId> = HashMap::new();

    let Some(file_state) = self.files.get(&file).cloned() else {
      return HashMap::new();
    };
    let mut resolved_defs = Vec::new();
    let mut bindings = file_state.bindings.clone();
    let mut exports = file_state.exports.clone();
    let reexports = file_state.reexports.clone();
    let export_all = file_state.export_all.clone();

    // `hir-js` definition order is not guaranteed to match source order (IDs
    // are content-derived). Align by spans to keep stable IDs wired to the
    // correct bound declaration when multiple defs share a name (e.g. globals
    // vs ambient modules).
    let mut lowered_defs: Vec<_> = lowered.defs.iter().collect();
    lowered_defs.sort_by_key(|def| (def.span.start, def.span.end, def.id.0));
    for def in lowered_defs {
      let raw_name = lowered
        .names
        .resolve(def.name)
        .unwrap_or_default()
        .to_string();
      // `hir-js` emits `VarDeclarator` defs as a container for the declaration
      // itself, alongside `Var` defs for the bound identifiers. Keep the
      // declarator defs addressable by ID, but avoid treating them as the named
      // binding to keep `definitions_in_file` name-based queries focused on
      // actual bindings.
      let is_var_declarator = def.path.kind == HirDefKind::VarDeclarator;
      let name = if is_var_declarator {
        format!("<var_decl:{raw_name}>")
      } else {
        raw_name.clone()
      };
      let match_kind = match_kind_from_hir(def.path.kind);
      // `hir-js` models variable declarations as a `VarDeclarator` node that owns the initializer
      // body plus one or more child `Var` defs for the bindings (to support destructuring).
      //
      // Track `VarDeclarator` as a definition for stable IDs, but do not treat it as a symbol in
      // any namespace or allow it to clobber the real `Var` binding in `bindings`/`exports`.
      let is_var_declarator = matches!(match_kind, DefMatchKind::VarDeclarator);
      let matched = by_name_kind
        .get_mut(&(name.clone(), match_kind))
        .and_then(|list| {
          if list.is_empty() {
            None
          } else {
            Some(list.remove(0))
          }
        });
      let (def_id, data) = if let Some((old_id, mut data)) = matched {
        id_mapping.insert(old_id, def.id);
        data.span = def.span;
        data.export = data.export || def.is_exported || def.is_default_export;
        if is_var_declarator {
          data.export = false;
        }
        match &mut data.kind {
          DefKind::Function(func) => func.body = def.body,
          DefKind::Var(var) => {
            if let Some(body) = def.body {
              var.body = body;
            }
          }
          DefKind::VarDeclarator(var) => {
            var.body = def.body;
          }
          DefKind::Class(class) => {
            class.body = def.body;
            class.declare |= def.is_ambient;
          }
          DefKind::Enum(en) => {
            en.body = def.body;
            en.declare |= def.is_ambient;
          }
          DefKind::Namespace(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          DefKind::Module(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          _ => {}
        }
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(def.id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(def.id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(def.id, params);
        }
        if let Some(decls) = self.interned_type_param_decls.get(&old_id).cloned() {
          new_interned_type_param_decls.insert(def.id, decls);
        }
        (def.id, data)
      } else {
        let symbol = self.alloc_symbol();
        let kind = match match_kind {
          DefMatchKind::Function => DefKind::Function(FuncData {
            params: def
              .body
              .and_then(|body_id| lowered.body(body_id))
              .and_then(|body| body.function.as_ref().map(|func| (body, func)))
              .map(|(body, func)| {
                func
                  .params
                  .iter()
                  .enumerate()
                  .map(|(index, param)| {
                    let name = match body.pats.get(param.pat.0 as usize).map(|pat| &pat.kind) {
                      Some(HirPatKind::Ident(name_id)) => lowered
                        .names
                        .resolve(*name_id)
                        .unwrap_or_default()
                        .to_string(),
                      _ => format!("<pattern{index}>"),
                    };
                    ParamData {
                      name,
                      typ: None,
                      symbol: self.alloc_symbol(),
                      pat: None,
                    }
                  })
                  .collect()
              })
              .unwrap_or_default(),
            return_ann: None,
            body: def.body,
          }),
          DefMatchKind::VarDeclarator => {
            DefKind::VarDeclarator(VarDeclaratorData { body: def.body })
          }
          DefMatchKind::Class => DefKind::Class(ClassData {
            body: def.body,
            instance_type: None,
            static_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Enum => DefKind::Enum(EnumData {
            body: def.body,
            is_const: false,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Namespace => DefKind::Namespace(NamespaceData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Module => DefKind::Module(ModuleData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Interface => DefKind::Interface(InterfaceData {
            typ: self.builtin.unknown,
          }),
          DefMatchKind::TypeAlias => DefKind::TypeAlias(TypeAliasData {
            typ: self.builtin.unknown,
          }),
          _ => DefKind::Var(VarData {
            typ: None,
            init: None,
            body: def.body.unwrap_or(MISSING_BODY),
            mode: VarDeclMode::Var,
          }),
        };
        let export = if is_var_declarator {
          false
        } else {
          def.is_exported || def.is_default_export
        };
        let data = DefData {
          name: name.clone(),
          file,
          span: def.span,
          symbol,
          export,
          kind,
        };
        self.record_def_symbol(def.id, symbol);
        if !is_var_declarator {
          self.record_symbol(file, def.span, symbol);
        }
        (def.id, data)
      };

      if !is_var_declarator {
        if is_file_level_binding(def) {
          bindings
            .entry(raw_name.clone())
            .and_modify(|binding| {
              binding.symbol = data.symbol;
              binding.def = Some(def_id);
            })
            .or_insert(SymbolBinding {
              symbol: data.symbol,
              def: Some(def_id),
              type_id: None,
            });
        }
      }

      if data.export && !is_var_declarator && is_file_level_binding(def) {
        let export_name = if def.is_default_export {
          "default".to_string()
        } else {
          raw_name.clone()
        };
        exports.insert(
          export_name,
          ExportEntry {
            symbol: data.symbol,
            def: Some(def_id),
            type_id: new_def_types.get(&def_id).copied(),
          },
        );
      }

      new_def_data.insert(def_id, data);
      resolved_defs.push(def_id);
    }

    for leftovers in by_name_kind.values_mut() {
      for (old_id, data) in leftovers.drain(..) {
        new_def_data.insert(old_id, data.clone());
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(old_id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(old_id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(old_id, params);
        }
        if let Some(decls) = self.interned_type_param_decls.get(&old_id).cloned() {
          new_interned_type_param_decls.insert(old_id, decls);
        }
      }
    }

    for binding in bindings.values_mut() {
      if let Some(def) = binding.def {
        if let Some(mapped) = id_mapping.get(&def) {
          binding.def = Some(*mapped);
        }
      }
    }
    for entry in exports.values_mut() {
      if let Some(def) = entry.def {
        if let Some(mapped) = id_mapping.get(&def) {
          entry.def = Some(*mapped);
        }
      }
    }

    // Synthesize value-side definitions for classes/enums so `typeof` can map to a
    // dedicated value def without conflating with the instance/type-side def.
    // These defs are stable across runs: they are derived from the type-side `DefId`.
    self.value_defs.retain(|type_def, value_def| {
      !file_def_ids.contains(type_def) && !file_def_ids.contains(value_def)
    });
    let mut taken_ids: HashSet<DefId> = new_def_data.keys().copied().collect();
    let mut class_enum_type_defs: Vec<DefId> = Vec::new();
    for def_id in resolved_defs.iter().copied() {
      if let Some(data) = new_def_data.get(&def_id) {
        if matches!(data.kind, DefKind::Class(_) | DefKind::Enum(_)) {
          class_enum_type_defs.push(def_id);
        }
      }
    }
    class_enum_type_defs.sort_by_key(|d| d.0);
    for type_def in class_enum_type_defs {
      let Some(type_data) = new_def_data.get(&type_def).cloned() else {
        continue;
      };
      let tag = match type_data.kind {
        DefKind::Class(_) => 1u32,
        DefKind::Enum(_) => 2u32,
        _ => continue,
      };
      let value_def = alloc_synthetic_def_id(
        file,
        &mut taken_ids,
        &("ts_value_def", file.0, type_def.0, tag),
      );
      self.value_defs.insert(type_def, value_def);
      new_def_data.entry(value_def).or_insert_with(|| DefData {
        name: type_data.name.clone(),
        file: type_data.file,
        span: type_data.span,
        symbol: type_data.symbol,
        export: type_data.export,
        kind: DefKind::Var(VarData {
          typ: None,
          init: None,
          body: MISSING_BODY,
          mode: VarDeclMode::Let,
        }),
      });
      if let Some(binding) = bindings.get_mut(&type_data.name) {
        if binding.def == Some(type_def) {
          binding.def = Some(value_def);
        }
      }
      for entry in exports.values_mut() {
        if entry.def == Some(type_def) {
          entry.def = Some(value_def);
        }
      }
    }

    self.files.insert(
      file,
      FileState {
        defs: resolved_defs,
        exports,
        bindings,
        top_body: file_state.top_body,
        reexports,
        export_all,
      },
    );

    self.def_data = new_def_data;
    self.def_types = new_def_types;
    self.interned_def_types = new_interned_def_types;
    self.interned_type_params = new_interned_type_params;
    self.interned_type_param_decls = new_interned_type_param_decls;

    self.symbol_to_def.clear();
    for (def, data) in self.def_data.iter() {
      self.symbol_to_def.insert(data.symbol, *def);
    }
    self.next_def = self
      .def_data
      .keys()
      .map(|d| d.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);

    id_mapping
  }

  fn map_hir_bodies(&mut self, file: FileId, lowered: &LowerResult) {
    // Bodies are keyed by stable hash-based IDs. In the (rare) event that a body id collides
    // across files, we must ensure we clear any stale metadata/parent edges before inserting the
    // newly-lowered bodies for `file`.
    let mut stale: HashSet<BodyId> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    stale.extend(lowered.body_index.keys().copied());
    self.body_map.retain(|id, _| !stale.contains(id));
    self.body_parents.retain(|child, _| !stale.contains(child));

    if let Some(state) = self.files.get_mut(&file) {
      state.top_body = Some(lowered.root_body());
    }

    let mut defs_by_span: HashMap<(TextRange, &'static str), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(String, &'static str), DefId> = HashMap::new();
    let mut file_defs: Vec<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .collect();
    file_defs.sort_by_key(|(id, data)| (data.span.start, data.span.end, id.0));
    for (def_id, data) in file_defs {
      let kind = match data.kind {
        DefKind::Function(_) => Some("fn"),
        DefKind::Var(_) => Some("var"),
        _ => None,
      };
      if let Some(kind) = kind {
        if kind == "var" {
          if let Some(hir_def) = lowered.def(*def_id) {
            if matches!(hir_def.path.kind, HirDefKind::VarDeclarator) {
              // `VarDeclarator` defs exist to own initializer bodies; they are not
              // bindings and shouldn't be used for mapping patterns to program
              // definitions.
              continue;
            }
          }
        }
        defs_by_span.entry((data.span, kind)).or_insert(*def_id);
        defs_by_name
          .entry((data.name.clone(), kind))
          .or_insert(*def_id);
      }
    }

    for (hir_body_id, idx) in lowered.body_index.iter() {
      let hir_body = lowered
        .bodies
        .get(*idx)
        .map(Arc::as_ref)
        .unwrap_or_else(|| panic!("missing lowered body for id {:?}", hir_body_id));

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Var(decl) = &stmt.kind {
          for declarator in decl.declarators.iter() {
            // Update every bound identifier in the declarator (including destructuring patterns)
            // with the initializer expression/body. This keeps `var_initializer` fast and avoids
            // relying on the salsa HIR scan for common destructuring cases.
            let mut stack = vec![declarator.pat];
            let mut updated: HashSet<DefId> = HashSet::new();
            while let Some(pat_id) = stack.pop() {
              let Some(pat) = hir_body.pats.get(pat_id.0 as usize) else {
                continue;
              };
              match &pat.kind {
                hir_js::PatKind::Ident(name_id) => {
                  let name = lowered.names.resolve(*name_id).map(|n| n.to_string());
                  let def_id = defs_by_span.get(&(pat.span, "var")).copied().or_else(|| {
                    name
                      .as_ref()
                      .and_then(|name| defs_by_name.get(&(name.clone(), "var")).copied())
                  });
                  let Some(def_id) = def_id else {
                    continue;
                  };
                  if !updated.insert(def_id) {
                    continue;
                  }
                  if let Some(def) = self.def_data.get_mut(&def_id) {
                    if let DefKind::Var(var) = &mut def.kind {
                      var.mode = match decl.kind {
                        hir_js::VarDeclKind::Var => VarDeclMode::Var,
                        hir_js::VarDeclKind::Let => VarDeclMode::Let,
                        hir_js::VarDeclKind::Const => VarDeclMode::Const,
                        hir_js::VarDeclKind::Using => VarDeclMode::Using,
                        hir_js::VarDeclKind::AwaitUsing => VarDeclMode::AwaitUsing,
                      };
                      if let Some(init) = declarator.init {
                        let prefer = matches!(hir_body.kind, HirBodyKind::Initializer);
                        if var.body == MISSING_BODY || prefer {
                          var.body = *hir_body_id;
                        }
                        if var.init.is_none() || prefer {
                          var.init = Some(init);
                        }
                      }
                    }
                  }
                }
                hir_js::PatKind::Array(arr) => {
                  for elem in arr.elements.iter() {
                    let Some(elem) = elem.as_ref() else {
                      continue;
                    };
                    stack.push(elem.pat);
                  }
                  if let Some(rest) = arr.rest {
                    stack.push(rest);
                  }
                }
                hir_js::PatKind::Object(obj) => {
                  for prop in obj.props.iter() {
                    stack.push(prop.value);
                  }
                  if let Some(rest) = obj.rest {
                    stack.push(rest);
                  }
                }
                hir_js::PatKind::Rest(inner) => {
                  stack.push(**inner);
                }
                hir_js::PatKind::Assign { target, .. } => {
                  stack.push(*target);
                }
                hir_js::PatKind::AssignTarget(_) => {}
              }
            }
          }
        }
      }

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Decl(def) = &stmt.kind {
          if let Some(hir_def) = lowered.def(*def) {
            if let Some(child) = hir_def.body {
              self.body_parents.insert(child, *hir_body_id);
            }
          }
        }
      }

      for expr in hir_body.exprs.iter() {
        match &expr.kind {
          HirExprKind::FunctionExpr { body, .. } | HirExprKind::ClassExpr { body, .. } => {
            self.body_parents.insert(*body, *hir_body_id);
          }
          _ => {}
        }
      }

      self.body_map.insert(
        *hir_body_id,
        BodyMeta {
          file,
          hir: Some(*hir_body_id),
          kind: hir_body.kind,
        },
      );
    }

    for export in lowered.hir.exports.iter() {
      if let HirExportKind::Default(default) = &export.kind {
        match &default.value {
          hir_js::ExportDefaultValue::Expr { expr, body } => {
            if let Some((_def_id, def)) = self
              .def_data
              .iter_mut()
              .find(|(_, data)| data.file == file && data.name == "default")
            {
              if let DefKind::Var(var) = &mut def.kind {
                var.body = *body;
                var.init = Some(*expr);
                var.mode = VarDeclMode::Const;
              }
              self.body_parents.insert(*body, lowered.root_body());
            }
          }
          hir_js::ExportDefaultValue::Class { def, body, .. }
          | hir_js::ExportDefaultValue::Function { def, body, .. } => {
            if let Some(data) = self.def_data.get_mut(def) {
              match &mut data.kind {
                DefKind::Function(func) => func.body = Some(*body),
                DefKind::Class(class) => class.body = Some(*body),
                _ => {}
              }
            }
            self.body_parents.insert(*body, lowered.root_body());
          }
        }
      }
    }

    // Connect definition-owned bodies (notably initializer bodies) to their containing body so
    // nested checks can seed outer bindings (parameters, locals, etc). Bodies introduced by
    // `StmtKind::Decl` and expression nodes are already linked above; this covers orphan bodies
    // such as `DefSource::Var` initializer bodies that otherwise lack a parent edge.
    let root_body = lowered.root_body();
    let mut def_to_body: HashMap<HirDefId, BodyId> = HashMap::new();
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
      self.body_parents.entry(child_body).or_insert(parent_body);
    }

    // Fallback: infer missing parent links from body span containment.
    //
    // `hir-js` synthesizes bodies for variable initializers (and similar nodes) that are not
    // referenced by the surrounding statement list. Those bodies still need parent edges so
    // nested checks can seed parameter/local bindings.
    fn hir_body_range(body: &hir_js::Body) -> TextRange {
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
        // Use the stored body span for synthesized bodies (notably initializer bodies) that don't
        // record statement/expression spans. This keeps span containment inference stable so
        // initializer bodies inherit bindings from their lexical parent.
        match body.kind {
          HirBodyKind::Class => TextRange::new(0, 0),
          _ => body.span,
        }
      } else {
        TextRange::new(start, end)
      }
    }

    let mut bodies: Vec<(BodyId, TextRange)> = lowered
      .body_index
      .keys()
      .copied()
      .filter_map(|id| lowered.body(id).map(|b| (id, hir_body_range(b))))
      .collect();
    bodies.sort_by_key(|(id, range)| (range.start, Reverse(range.end), id.0));

    let mut stack: Vec<(BodyId, TextRange)> = Vec::new();
    for (child, range) in bodies {
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
          .map(|body| matches!(body.kind, HirBodyKind::Initializer))
          .unwrap_or(false);
        // Initializer bodies must inherit bindings from their containing scope
        // (e.g. function parameters). The def-parent chain can be incomplete or
        // point at a broader container, so prefer the lexical parent inferred
        // from span containment for initializer bodies.
        if is_initializer || !self.body_parents.contains_key(&child) {
          self.body_parents.insert(child, computed_parent);
        }
      }
      stack.push((child, range));
    }

    // Keep the body parent graph consistent with the query-side computation used
    // by `db::body_parents_in_file`. The salsa query includes additional edges
    // (e.g. getter/setter bodies and synthesized initializer bodies) and is the
    // canonical implementation. Overwrite any locally inferred edges for this
    // file so nested checks can reliably seed outer bindings.
    let parents = db::body_parents_in_file(&self.typecheck_db, file);
    for (child, parent) in parents.iter() {
      self.body_parents.insert(*child, *parent);
    }

    self.next_body = self
      .body_map
      .keys()
      .map(|b| b.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  fn rebuild_body_owners(&mut self) {
    self.body_owners.clear();
    let mut defs: Vec<_> = self.def_data.iter().collect();
    defs.sort_by_key(|(id, data)| (data.file.0, data.span.start, data.span.end, id.0));
    for (def_id, data) in defs {
      match &data.kind {
        DefKind::Function(func) => {
          if let Some(body) = func.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Var(var) => {
          if var.body != MISSING_BODY {
            self.body_owners.insert(var.body, *def_id);
          }
        }
        DefKind::VarDeclarator(var) => {
          if let Some(body) = var.body {
            self.body_owners.entry(body).or_insert(*def_id);
          }
        }
        DefKind::Class(class) => {
          if let Some(body) = class.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Enum(en) => {
          if let Some(body) = en.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Namespace(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Module(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Import(_)
        | DefKind::ImportAlias(_)
        | DefKind::Interface(_)
        | DefKind::TypeAlias(_) => {}
      }
    }
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

  fn push_semantic_diagnostics(&mut self, diags: Vec<Diagnostic>) {
    for mut diag in diags {
      if diag.code == "BIND1002" {
        continue;
      }
      if diag.code == "BIND1002" && diag.message.contains("unresolved import:") {
        if let Some(spec) = diag.message.split(':').nth(1).map(|s| s.trim()) {
          let has_ambient = self
            .semantics
            .as_ref()
            .and_then(|semantics| semantics.exports_of_ambient_module(spec))
            .map(|exports| !exports.is_empty())
            .unwrap_or(false);
          if has_ambient {
            continue;
          }
        }
      }
      if diag.code == "BIND1002" {
        if diag.message.contains("unresolved") {
          diag.code = codes::UNRESOLVED_MODULE.as_str().into();
        } else {
          diag.code = codes::UNKNOWN_EXPORT.as_str().into();
        }
      }
      let duplicate = self.diagnostics.iter().any(|existing| {
        existing.code == diag.code
          && existing.primary == diag.primary
          && existing.message == diag.message
      });
      if duplicate {
        continue;
      }
      self.diagnostics.push(diag);
    }
  }

  fn check_import_assignment_requires(&mut self) {
    // Match tsc's TS1202 behaviour: `import x = require("...")` is rejected when
    // targeting ECMAScript module outputs.
    //
    // Note: `tsc` only allows `import = require()` in ESM output modes for the
    // Node16/NodeNext emit strategies, and only when importing from a
    // CommonJS-style module (one that uses `export =`).
    let module =
      self
        .compiler_options
        .module
        .unwrap_or_else(|| match self.compiler_options.target {
          ScriptTarget::Es3 | ScriptTarget::Es5 => ModuleKind::CommonJs,
          _ => ModuleKind::Es2015,
        });
    let targets_ecmascript_modules = matches!(
      module,
      ModuleKind::Es2015
        | ModuleKind::Es2020
        | ModuleKind::Es2022
        | ModuleKind::EsNext
        | ModuleKind::Node16
        | ModuleKind::NodeNext
    );
    if !targets_ecmascript_modules {
      return;
    }

    let Some(semantics) = self.semantics.as_ref() else {
      return;
    };

    let allow_commonjs_interop = matches!(module, ModuleKind::Node16 | ModuleKind::NodeNext);
    let mut records = self.import_assignment_requires.clone();
    records.sort_by_key(|record| (record.file.0, record.span.start, record.span.end));
    for record in records {
      // TypeScript permits `import = require()` declarations in `.d.ts` files
      // regardless of emit target. Since these files never produce JS output,
      // the restriction only applies to emit-capable sources.
      if self.file_kinds.get(&record.file) == Some(&FileKind::Dts) {
        continue;
      }
      if allow_commonjs_interop {
        let has_export_assignment = match record.target {
          ImportTarget::File(target_file) => semantics
            .exports_of_opt(sem_ts::FileId(target_file.0))
            .map(|exports| exports.contains_key("export="))
            .unwrap_or(false),
          ImportTarget::Unresolved { .. } => false,
        };
        if has_export_assignment {
          continue;
        }
      }
      self.diagnostics.push(codes::IMPORT_ASSIGNMENT_IN_ESM.error(
        "Import assignment cannot be used when targeting ECMAScript modules.",
        Span::new(record.file, record.span),
      ));
    }
  }

  fn check_export_assignments_in_esm(&mut self) {
    // Match tsc's TS1203 behaviour: `export = value` is rejected when emitting
    // ECMAScript modules.
    let module =
      self
        .compiler_options
        .module
        .unwrap_or_else(|| match self.compiler_options.target {
          ScriptTarget::Es3 | ScriptTarget::Es5 => ModuleKind::CommonJs,
          _ => ModuleKind::Es2015,
        });
    let targets_ecmascript_modules = matches!(
      module,
      ModuleKind::Es2015
        | ModuleKind::Es2020
        | ModuleKind::Es2022
        | ModuleKind::EsNext
        | ModuleKind::Node16
        | ModuleKind::NodeNext
    );
    if !targets_ecmascript_modules {
      return;
    }

    let mut files: Vec<FileId> = self.hir_lowered.keys().copied().collect();
    files.sort_by_key(|file| file.0);
    for file in files {
      // TypeScript permits `export =` declarations in `.d.ts` files regardless
      // of emit target. Since these files never produce JS output, the
      // restriction only applies to emit-capable sources.
      if self.file_kinds.get(&file) == Some(&FileKind::Dts) {
        continue;
      }
      let Some(lowered) = self.hir_lowered.get(&file) else {
        continue;
      };
      for export in lowered.hir.exports.iter() {
        if matches!(export.kind, hir_js::ExportKind::Assignment(_)) {
          self.diagnostics.push(codes::EXPORT_ASSIGNMENT_IN_ESM.error(
            "Export assignment cannot be used when targeting ECMAScript modules.",
            Span::new(file, export.span),
          ));
        }
      }
    }
  }

  fn resolve_reexports(&mut self) {
    let mut changed = true;
    let mut files: Vec<FileId> = self.files.keys().copied().collect();
    files.sort_by_key(|f| f.0);
    while changed {
      changed = false;
      for file in files.iter() {
        let Some(state) = self.files.get(file).cloned() else {
          continue;
        };
        let mut exports = state.exports.clone();
        for spec in state.reexports.iter() {
          let Ok(target_exports) = self.exports_of_file(spec.from) else {
            continue;
          };
          if let Some(entry) = target_exports.get(&spec.original) {
            let resolved_def = entry
              .def
              .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
            if !spec.type_only {
              if let Some(def) = resolved_def {
                if let Some(def_data) = self.def_data.get(&def) {
                  if matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
                    let duplicate = self.diagnostics.iter().any(|existing| {
                      existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
                        && existing.primary.file == *file
                        && existing.primary.range == spec.span
                    });
                    if !duplicate {
                      self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                        format!("unknown export {}", spec.original),
                        Span::new(*file, spec.span),
                      ));
                    }
                    continue;
                  }
                }
              }
            }
            let mut type_id = entry.type_id;
            if let Some(def) = resolved_def {
              match self.export_type_for_def(def) {
                Ok(Some(ty)) => type_id = Some(ty),
                Ok(None) => {
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
                Err(fatal) => {
                  self.diagnostics.push(fatal_to_diagnostic(fatal));
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
              }
            }
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(&spec.alias) {
              if existing.symbol != mapped.symbol {
                update = false;
              } else if existing.def.is_none() && mapped.def.is_some() {
                update = true;
              } else if existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
              let previous = exports.insert(spec.alias.clone(), mapped.clone());
              if previous
                .as_ref()
                .map(|prev| {
                  prev.symbol != mapped.symbol
                    || prev.def != mapped.def
                    || prev.type_id != mapped.type_id
                })
                .unwrap_or(true)
              {
                changed = true;
              }
            }
            continue;
          }
          let duplicate = self.diagnostics.iter().any(|existing| {
            existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
              && existing.primary.file == *file
              && existing.primary.range == spec.span
          });
          if !duplicate {
            self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
              format!("unknown export {}", spec.original),
              Span::new(*file, spec.span),
            ));
          }
        }

        for spec in state.export_all.iter() {
          let Ok(target_exports) = self.exports_of_file(spec.from) else {
            continue;
          };
          for (name, entry) in target_exports.iter() {
            if name == "default" {
              continue;
            }
            let mut is_type = false;
            let resolved_def = entry
              .def
              .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
            if let Some(def) = resolved_def {
              if let Some(def_data) = self.def_data.get(&def) {
                is_type = matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_));
                if !spec.type_only && is_type {
                  continue;
                }
              }
            }
            if spec.type_only && !is_type {
              continue;
            }
            let mut type_id = entry.type_id;
            if let Some(def) = resolved_def {
              match self.export_type_for_def(def) {
                Ok(Some(ty)) => type_id = Some(ty),
                Ok(None) => {
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
                Err(fatal) => {
                  self.diagnostics.push(fatal_to_diagnostic(fatal));
                  if type_id.is_none() {
                    type_id = self.def_types.get(&def).copied();
                  }
                }
              }
            }
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(name) {
              if existing.symbol != mapped.symbol {
                update = false;
              } else if existing.def.is_none() && mapped.def.is_some() {
                update = true;
              } else if existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
              let previous = exports.insert(name.clone(), mapped.clone());
              if previous
                .as_ref()
                .map(|prev| {
                  prev.symbol != mapped.symbol
                    || prev.def != mapped.def
                    || prev.type_id != mapped.type_id
                })
                .unwrap_or(true)
              {
                changed = true;
              }
            }
          }
        }

        if let Some(existing) = self.files.get_mut(file) {
          existing.exports = exports;
        }
      }
    }
  }

  fn export_type_for_def(&mut self, def: DefId) -> Result<Option<TypeId>, FatalError> {
    self.rebuild_callable_overloads();
    if let Some(store) = self.interned_store.clone() {
      let mut cache = HashMap::new();
      if let Some(merged) = self.callable_overload_type_for_def(def, &store, &mut cache) {
        return Ok(Some(merged));
      }
      if let Some(defs) = self.callable_overload_defs(def) {
        if defs.len() > 1 {
          if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache) {
            return Ok(Some(merged));
          }
        }
      }
      let needs_recompute = match self.def_types.get(&def).copied() {
        Some(existing) => {
          let in_bounds = self.type_store.contains_id(existing);
          !(in_bounds && !matches!(self.type_store.kind(existing), TypeKind::Unknown))
        }
        None => true,
      };
      if needs_recompute {
        self.type_of_def(def)?;
      }
      if let Some(ty) = self.interned_def_types.get(&def).copied() {
        if !matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown) {
          return Ok(Some(ty));
        }
      }
      let Some(store_ty) = self.def_types.get(&def).copied() else {
        return Ok(None);
      };
      let interned = convert_type_for_display(store_ty, self, &store, &mut cache);
      let interned = store.canon(interned);
      self.interned_def_types.insert(def, interned);
      Ok(Some(interned))
    } else {
      let needs_recompute = match self.def_types.get(&def).copied() {
        Some(existing) => {
          let in_bounds = self.type_store.contains_id(existing);
          !(in_bounds && !matches!(self.type_store.kind(existing), TypeKind::Unknown))
        }
        None => true,
      };
      if needs_recompute {
        self.type_of_def(def)?;
      }
      Ok(self.def_types.get(&def).copied())
    }
  }

  fn import_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref().cloned() else {
      return self.builtin.unknown;
    };
    use tti::TypeKind as InternedKind;
    match store.type_kind(ty) {
      InternedKind::Any => self.builtin.any,
      InternedKind::Unknown => self.builtin.unknown,
      InternedKind::Never => self.builtin.never,
      InternedKind::Void => self.builtin.void,
      InternedKind::Null => self.builtin.null,
      InternedKind::Undefined => self.builtin.undefined,
      InternedKind::Boolean => self.builtin.boolean,
      InternedKind::Number => self.builtin.number,
      InternedKind::String => self.builtin.string,
      InternedKind::BooleanLiteral(value) => self.type_store.literal_boolean(value),
      InternedKind::NumberLiteral(value) => self.type_store.literal_number(value.to_string()),
      InternedKind::StringLiteral(name) => {
        let name = store.name(name);
        self.type_store.literal_string(name)
      }
      InternedKind::Tuple(elems) => {
        let readonly = elems.iter().all(|elem| elem.readonly);
        let members: Vec<_> = elems
          .iter()
          .map(|elem| self.import_interned_type(elem.ty))
          .collect();
        self.type_store.tuple(members, readonly)
      }
      InternedKind::Array { ty, .. } => {
        let inner = self.import_interned_type(ty);
        self.type_store.array(inner)
      }
      InternedKind::Union(types) => {
        let mapped: Vec<_> = types
          .iter()
          .map(|t| self.import_interned_type(*t))
          .collect();
        self.type_store.union(mapped, &self.builtin)
      }
      InternedKind::Object(obj) => {
        let obj = store.object(obj);
        let shape = store.shape(obj.shape);
        let mut legacy = ObjectType::empty();
        for prop in shape.properties {
          let name = match prop.key {
            tti::PropKey::String(id) | tti::PropKey::Symbol(id) => Some(store.name(id)),
            tti::PropKey::Number(num) => Some(num.to_string()),
          };
          if let Some(name) = name {
            legacy.props.insert(
              name,
              ObjectProperty {
                typ: self.import_interned_type(prop.data.ty),
                optional: prop.data.optional,
                readonly: prop.data.readonly,
              },
            );
          }
        }
        for indexer in shape.indexers {
          let value = self.import_interned_type(indexer.value_type);
          match store.type_kind(indexer.key_type) {
            InternedKind::String => legacy.string_index = Some(value),
            InternedKind::Number => legacy.number_index = Some(value),
            _ => {}
          }
        }
        self.type_store.object(legacy)
      }
      InternedKind::Predicate {
        parameter,
        asserted,
        asserts,
      } => {
        let param = match parameter {
          Some(tti::PredicateParam::This) => "this".to_string(),
          _ => String::new(),
        };
        let asserted = asserted.map(|ty| self.import_interned_type(ty));
        self.type_store.predicate(param, asserted, asserts)
      }
      InternedKind::Callable { overloads } => {
        let mut fns = Vec::new();
        for sig_id in overloads {
          let sig = store.signature(sig_id);
          let params = sig
            .params
            .iter()
            .map(|param| self.import_interned_type(param.ty))
            .collect();
          let ret = self.import_interned_type(sig.ret);
          fns.push(self.type_store.function(params, ret));
        }
        if fns.is_empty() {
          self.builtin.unknown
        } else {
          self.type_store.union(fns, &self.builtin)
        }
      }
      _ => self.builtin.unknown,
    }
  }

  fn ensure_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    if store.contains_type_id(ty) {
      return store.canon(ty);
    }
    if let Some(mapped) = self.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        self.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return store.canon(mapped);
    }
    let mut cache = HashMap::new();
    let interned = convert_type_for_display(ty, self, store, &mut cache);
    store.canon(interned)
  }

  fn is_unknown_type_id(&self, ty: TypeId) -> bool {
    if self.type_store.contains_id(ty) {
      return matches!(self.type_store.kind(ty), TypeKind::Unknown);
    }
    if let Some(store) = self.interned_store.as_ref() {
      if store.contains_type_id(ty) {
        return matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
      }
    }
    true
  }

  fn prefer_named_refs(&self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    self.prefer_named_refs_in_store(store, ty)
  }

  fn prefer_named_refs_in_store(&self, store: &Arc<tti::TypeStore>, ty: TypeId) -> TypeId {
    let canonical = store.canon(ty);
    let kind = store.type_kind(canonical);
    let primitive_like = matches!(
      kind,
      tti::TypeKind::Any
        | tti::TypeKind::Unknown
        | tti::TypeKind::Never
        | tti::TypeKind::Void
        | tti::TypeKind::Null
        | tti::TypeKind::Undefined
        | tti::TypeKind::Boolean
        | tti::TypeKind::Number
        | tti::TypeKind::String
        | tti::TypeKind::BigInt
        | tti::TypeKind::Symbol
        | tti::TypeKind::UniqueSymbol
        | tti::TypeKind::Callable { .. }
        | tti::TypeKind::BooleanLiteral(_)
        | tti::TypeKind::NumberLiteral(_)
        | tti::TypeKind::StringLiteral(_)
        | tti::TypeKind::BigIntLiteral(_)
        | tti::TypeKind::This
        | tti::TypeKind::TypeParam(_)
    );
    if !primitive_like {
      if let Some(def) = self.interned_named_def_types.get(&canonical).copied() {
        let mut args = self
          .interned_type_params
          .get(&def)
          .cloned()
          .unwrap_or_default();
        args.sort_by_key(|param| param.0);
        let args: Vec<_> = args
          .into_iter()
          .map(|param| store.intern_type(tti::TypeKind::TypeParam(param)))
          .collect();
        return store.canon(store.intern_type(tti::TypeKind::Ref { def, args }));
      }
    }
    match kind {
      tti::TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.union(mapped);
      }
      tti::TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.intersection(mapped);
      }
      tti::TypeKind::Array { ty, readonly } => {
        let mapped = self.prefer_named_refs_in_store(store, ty);
        if mapped != ty {
          return store.intern_type(tti::TypeKind::Array {
            ty: mapped,
            readonly,
          });
        }
      }
      tti::TypeKind::Tuple(elems) => {
        let mut changed = false;
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| {
            let mapped = self.prefer_named_refs_in_store(store, elem.ty);
            changed |= mapped != elem.ty;
            tti::TupleElem {
              ty: mapped,
              optional: elem.optional,
              rest: elem.rest,
              readonly: elem.readonly,
            }
          })
          .collect();
        if changed {
          return store.intern_type(tti::TypeKind::Tuple(mapped));
        }
      }
      _ => {}
    }
    canonical
  }

  fn prefer_named_class_refs_in_store(&self, store: &Arc<tti::TypeStore>, ty: TypeId) -> TypeId {
    let canonical = store.canon(ty);
    let kind = store.type_kind(canonical);
    let primitive_like = matches!(
      kind,
      tti::TypeKind::Any
        | tti::TypeKind::Unknown
        | tti::TypeKind::Never
        | tti::TypeKind::Void
        | tti::TypeKind::Null
        | tti::TypeKind::Undefined
        | tti::TypeKind::Boolean
        | tti::TypeKind::Number
        | tti::TypeKind::String
        | tti::TypeKind::BigInt
        | tti::TypeKind::Symbol
        | tti::TypeKind::UniqueSymbol
        | tti::TypeKind::Callable { .. }
        | tti::TypeKind::BooleanLiteral(_)
        | tti::TypeKind::NumberLiteral(_)
        | tti::TypeKind::StringLiteral(_)
        | tti::TypeKind::BigIntLiteral(_)
        | tti::TypeKind::This
        | tti::TypeKind::TypeParam(_)
    );
    if !primitive_like {
      if let Some(def) = self.interned_named_def_types.get(&canonical).copied() {
        if self
          .def_data
          .get(&def)
          .is_some_and(|data| matches!(data.kind, DefKind::Class(_)))
        {
          let mut args = self
            .interned_type_params
            .get(&def)
            .cloned()
            .unwrap_or_default();
          args.sort_by_key(|param| param.0);
          let args: Vec<_> = args
            .into_iter()
            .map(|param| store.intern_type(tti::TypeKind::TypeParam(param)))
            .collect();
          return store.canon(store.intern_type(tti::TypeKind::Ref { def, args }));
        }
      }
    }
    match kind {
      tti::TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_class_refs_in_store(store, member))
          .collect();
        return store.union(mapped);
      }
      tti::TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_class_refs_in_store(store, member))
          .collect();
        return store.intersection(mapped);
      }
      tti::TypeKind::Array { ty, readonly } => {
        let mapped = self.prefer_named_class_refs_in_store(store, ty);
        if mapped != ty {
          return store.intern_type(tti::TypeKind::Array {
            ty: mapped,
            readonly,
          });
        }
      }
      tti::TypeKind::Tuple(elems) => {
        let mut changed = false;
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| {
            let mapped = self.prefer_named_class_refs_in_store(store, elem.ty);
            changed |= mapped != elem.ty;
            tti::TupleElem {
              ty: mapped,
              optional: elem.optional,
              rest: elem.rest,
              readonly: elem.readonly,
            }
          })
          .collect();
        if changed {
          return store.intern_type(tti::TypeKind::Tuple(mapped));
        }
      }
      _ => {}
    }
    canonical
  }

  fn resolve_value_ref_type(&mut self, ty: TypeId) -> Result<TypeId, FatalError> {
    let Some(store) = self.interned_store.clone() else {
      return Ok(ty);
    };
    if std::env::var("DEBUG_OVERLOAD").is_ok() {
      if store.contains_type_id(ty) {
        eprintln!(
          "DEBUG resolve_value_ref_type input kind {:?}",
          store.type_kind(store.canon(ty))
        );
      } else {
        eprintln!("DEBUG resolve_value_ref_type input not in store");
      }
    }
    if !store.contains_type_id(ty) {
      return Ok(ty);
    }
    let canonical = store.canon(ty);
    if let tti::TypeKind::Ref { def, args } = store.type_kind(canonical) {
      if args.is_empty() {
        let def_id = DefId(def.0);
        if self.type_stack.contains(&def_id) {
          return Ok(canonical);
        }
        let should_resolve = self
          .def_data
          .get(&def_id)
          .map(|data| {
            matches!(
              data.kind,
              DefKind::Function(_)
                | DefKind::Var(_)
                | DefKind::Class(_)
                | DefKind::Enum(_)
                | DefKind::Namespace(_)
                | DefKind::Module(_)
                | DefKind::Import(_)
            )
          })
          .unwrap_or(false);
        if should_resolve {
          if std::env::var("DEBUG_OVERLOAD").is_ok() {
            if let Some(data) = self.def_data.get(&def_id) {
              eprintln!(
                "DEBUG resolve_value_ref_type ref to {} {:?}",
                data.name, data.kind
              );
            }
          }
          let resolved = self.type_of_def(def_id)?;
          let resolved = self.ensure_interned_type(resolved);
          if std::env::var("DEBUG_OVERLOAD").is_ok() {
            eprintln!(
              "DEBUG resolve_value_ref_type resolved kind {:?}",
              store.type_kind(resolved)
            );
          }
          if !matches!(store.type_kind(resolved), tti::TypeKind::Unknown) {
            return Ok(store.canon(resolved));
          }
        }
      }
    }
    Ok(canonical)
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      _ => ty,
    }
  }

  fn widen_union_literals(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      TypeKind::Union(types) => {
        let members: Vec<_> = types
          .into_iter()
          .map(|t| self.widen_union_literals(t))
          .collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  fn widen_array_elements(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(*inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  fn widen_object_literal(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::Object(mut obj) => {
        let mut changed = false;
        for prop in obj.props.values_mut() {
          if prop.readonly {
            continue;
          }
          let widened = self.widen_union_literals(prop.typ);
          if widened != prop.typ {
            prop.typ = widened;
            changed = true;
          }
        }
        if let Some(value) = obj.string_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.string_index = Some(widened);
            changed = true;
          }
        }
        if let Some(value) = obj.number_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.number_index = Some(widened);
            changed = true;
          }
        }
        if changed {
          self.type_store.object(obj)
        } else {
          ty
        }
      }
      _ => ty,
    }
  }

  fn init_is_satisfies(&self, body: BodyId, expr: ExprId) -> bool {
    let meta = match self.body_map.get(&body) {
      Some(meta) => meta,
      None => return false,
    };
    let hir_id = match meta.hir {
      Some(id) => id,
      None => return false,
    };
    let lowered = match self.hir_lowered.get(&meta.file) {
      Some(lowered) => lowered,
      None => return false,
    };
    let hir_body = match lowered.body(hir_id) {
      Some(body) => body,
      None => return false,
    };
    hir_body
      .exprs
      .get(expr.0 as usize)
      .map(|e| matches!(e.kind, HirExprKind::Satisfies { .. }))
      .unwrap_or(false)
  }

  fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    if let Some(def_data) = self.def_data.get(&def) {
      if let DefKind::Var(var) = &def_data.kind {
        if var.body != MISSING_BODY {
          if let Some(expr) = var.init {
            let decl_kind = match var.mode {
              VarDeclMode::Var => HirVarDeclKind::Var,
              VarDeclMode::Let => HirVarDeclKind::Let,
              VarDeclMode::Const => HirVarDeclKind::Const,
              VarDeclMode::Using => HirVarDeclKind::Using,
              VarDeclMode::AwaitUsing => HirVarDeclKind::AwaitUsing,
            };
            let pat = if self.snapshot_loaded {
              self
                .body_results
                .get(&var.body)
                .and_then(|result| {
                  result
                    .pat_spans
                    .iter()
                    .position(|span| *span == def_data.span)
                })
                .map(|idx| PatId(idx as u32))
            } else {
              self.body_map.get(&var.body).and_then(|meta| {
                let hir_id = meta.hir?;
                self
                  .hir_lowered
                  .get(&meta.file)
                  .and_then(|lowered| lowered.body(hir_id))
                  .and_then(|body| {
                    body.pats.iter().enumerate().find_map(|(idx, pat)| {
                      (pat.span == def_data.span).then_some(PatId(idx as u32))
                    })
                  })
              })
            };
            return Some(VarInit {
              body: var.body,
              expr,
              decl_kind,
              pat,
              span: Some(def_data.span),
            });
          }
        }
      }
    }

    if self.snapshot_loaded {
      return None;
    }

    if let Some(init) = crate::db::var_initializer(&self.typecheck_db, def) {
      if std::env::var("DEBUG_OVERLOAD").is_ok() {
        if let Some(data) = self.def_data.get(&def) {
          eprintln!("DEBUG var initializer for {} -> {:?}", data.name, init);
        }
      }
      return Some(init);
    }

    let def_data = self.def_data.get(&def)?;
    let lowered = self.hir_lowered.get(&def_data.file)?;
    let hir_def = lowered.def(def)?;
    let def_name = lowered.names.resolve(hir_def.path.name);
    if !matches!(
      hir_def.path.kind,
      HirDefKind::Var | HirDefKind::VarDeclarator
    ) && def_name != Some("default")
    {
      return None;
    }
    let def_name = def_name.or_else(|| Some(def_data.name.as_str()));
    var_initializer_in_file(lowered, def, hir_def.span, def_name)
  }

  fn declared_type_for_span(&mut self, file: FileId, target: TextRange) -> Option<TypeId> {
    fn walk_namespace(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      target: TextRange,
    ) -> Option<TypeId> {
      match body {
        NamespaceBody::Block(stmts) => walk(state, file, stmts, target),
        NamespaceBody::Namespace(inner) => walk_namespace(state, file, &inner.stx.body, target),
      }
    }

    fn walk(
      state: &mut ProgramState,
      file: FileId,
      stmts: &[Node<Stmt>],
      target: TextRange,
    ) -> Option<TypeId> {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::AmbientVarDecl(var) => {
            let span = loc_to_span(file, stmt.loc).range;
            if span == target {
              if let Some(ann) = var.stx.type_annotation.as_ref() {
                return Some(state.lower_interned_type_expr(file, ann));
              }
            }
          }
          Stmt::VarDecl(var) => {
            // Most definitions use the binding pattern span, but some def IDs
            // (notably for local variables) may be keyed by a wider span (e.g.
            // the declarator span). Prefer the exact pattern match first, then
            // fall back to a single unambiguous declarator whose span contains
            // the target.
            for decl in var.stx.declarators.iter() {
              let pat_span = loc_to_span(file, decl.pattern.stx.pat.loc).range;
              if pat_span == target {
                if let Some(ann) = decl.type_annotation.as_ref() {
                  return Some(state.lower_interned_type_expr(file, ann));
                }
              }
            }

            let mut matching_decl = None;
            for decl in var.stx.declarators.iter() {
              let pat_span = loc_to_span(file, decl.pattern.stx.pat.loc).range;
              let end = decl
                .initializer
                .as_ref()
                .map(|init| loc_to_span(file, init.loc).range.end)
                .or_else(|| {
                  decl
                    .type_annotation
                    .as_ref()
                    .map(|ann| loc_to_span(file, ann.loc).range.end)
                })
                .unwrap_or(pat_span.end);
              let decl_span = TextRange::new(pat_span.start, end);
              // Some defs may be keyed by a span that covers the full declarator
              // (or even the full statement). Prefer matching those wider spans,
              // but avoid matching arbitrary sub-spans inside the pattern (e.g.
              // bindings within destructuring patterns).
              let matches = decl_span == target
                || (target.start <= decl_span.start && target.end >= decl_span.end)
                || (target.start == decl_span.start && target.end <= decl_span.end)
                || (target.start <= pat_span.start && target.end >= pat_span.end);
              if matches {
                if matching_decl.is_some() {
                  matching_decl = None;
                  break;
                }
                matching_decl = Some(decl);
              }
            }

            if let Some(decl) = matching_decl {
              if let Some(ann) = decl.type_annotation.as_ref() {
                return Some(state.lower_interned_type_expr(file, ann));
              }
            }
          }
          Stmt::Block(block) => {
            if let Some(ty) = walk(state, file, &block.stx.body, target) {
              return Some(ty);
            }
          }
          Stmt::NamespaceDecl(ns) => {
            if let Some(ty) = walk_namespace(state, file, &ns.stx.body, target) {
              return Some(ty);
            }
          }
          Stmt::ModuleDecl(module) => {
            if let Some(body) = &module.stx.body {
              if let Some(ty) = walk(state, file, body, target) {
                return Some(ty);
              }
            }
          }
          Stmt::GlobalDecl(global) => {
            if let Some(ty) = walk(state, file, &global.stx.body, target) {
              return Some(ty);
            }
          }
          _ => {}
        }
      }
      None
    }

    let ast = match self.asts.get(&file) {
      Some(ast) => ast.clone(),
      None => return None,
    };
    walk(self, file, &ast.stx.body, target)
  }

  fn lower_interned_type_expr(&mut self, file: FileId, expr: &Node<TypeExpr>) -> TypeId {
    let Some(store) = self.interned_store.clone() else {
      return self.type_from_type_expr(expr);
    };

    let prev_file = self.current_file;
    self.current_file = Some(file);

    let mut binding_defs = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        if let Some(def) = binding.def {
          binding_defs.insert(name.clone(), def);
        }
      }
    }
    let resolver = self.build_type_resolver(&binding_defs);
    let mut lowerer = TypeLowerer::new(Arc::clone(&store));
    lowerer.set_file(file);
    lowerer.set_resolver(resolver);
    let ty = store.canon(lowerer.lower_type_expr(expr));
    self.diagnostics.extend(lowerer.take_diagnostics());

    self.current_file = prev_file;
    ty
  }

  fn type_alias_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
    name: &str,
  ) -> Option<TypeId> {
    fn walk_namespace(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      target: TextRange,
      name: &str,
    ) -> Option<TypeId> {
      match body {
        NamespaceBody::Block(stmts) => walk(state, file, stmts, target, name),
        NamespaceBody::Namespace(inner) => {
          walk_namespace(state, file, &inner.stx.body, target, name)
        }
      }
    }

    fn walk(
      state: &mut ProgramState,
      file: FileId,
      stmts: &[Node<Stmt>],
      target: TextRange,
      name: &str,
    ) -> Option<TypeId> {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::TypeAliasDecl(alias) => {
            let span = loc_to_span(file, stmt.loc).range;
            if span == target || alias.stx.name == name {
              let ty = state.lower_interned_type_expr(file, &alias.stx.type_expr);
              return Some(ty);
            }
          }
          Stmt::Block(block) => {
            if let Some(ty) = walk(state, file, &block.stx.body, target, name) {
              return Some(ty);
            }
          }
          Stmt::NamespaceDecl(ns) => {
            if let Some(ty) = walk_namespace(state, file, &ns.stx.body, target, name) {
              return Some(ty);
            }
          }
          Stmt::GlobalDecl(global) => {
            if let Some(ty) = walk(state, file, &global.stx.body, target, name) {
              return Some(ty);
            }
          }
          _ => {}
        }
      }
      None
    }

    let ast = match self.asts.get(&file) {
      Some(ast) => ast.clone(),
      None => return None,
    };
    walk(self, file, &ast.stx.body, target, name)
  }

  fn resolve_import_alias_target_in_namespace(
    &self,
    file: FileId,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let resolve_via_semantics = || -> Option<DefId> {
      let semantics = self.semantics.as_ref()?;
      let sem_file = sem_ts::FileId(file.0);
      if path.is_empty() {
        return None;
      }

      let global_symbol = |name: &str, ns: sem_ts::Namespace| -> Option<sem_ts::SymbolId> {
        semantics
          .global_symbols()
          .get(name)
          .and_then(|group| group.symbol_for(ns, semantics.symbols()))
      };

      let symbol = semantics
        .resolve_in_module(sem_file, &path[0], sem_ts::Namespace::NAMESPACE)
        .or_else(|| semantics.resolve_in_module(sem_file, &path[0], final_ns))
        .or_else(|| semantics.resolve_in_module(sem_file, &path[0], sem_ts::Namespace::VALUE))
        .or_else(|| global_symbol(&path[0], sem_ts::Namespace::NAMESPACE))
        .or_else(|| global_symbol(&path[0], final_ns))
        .or_else(|| global_symbol(&path[0], sem_ts::Namespace::VALUE))?;

      let pick_def = |symbol: sem_ts::SymbolId, ns: sem_ts::Namespace| -> Option<DefId> {
        let symbols = semantics.symbols();
        let mut best: Option<(u8, usize, DefId)> = None;
        for (idx, decl_id) in semantics.symbol_decls(symbol, ns).iter().enumerate() {
          let decl = symbols.decl(*decl_id);
          let Some(def) = self.map_decl_to_program_def(decl, ns) else {
            continue;
          };
          let pri = self.def_priority(def, ns);
          if pri == u8::MAX {
            continue;
          }
          let key = (pri, idx, def);
          best = match best {
            Some((best_pri, best_idx, best_def)) if (best_pri, best_idx, best_def) <= key => {
              Some((best_pri, best_idx, best_def))
            }
            _ => Some(key),
          };
        }
        best.map(|(_, _, def)| def)
      };

      if path.len() == 1 {
        return pick_def(symbol, final_ns)
          .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
          .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
      }

      let sym_data = semantics.symbols().symbol(symbol);
      let imported_name = match &sym_data.origin {
        sem_ts::SymbolOrigin::Import { imported, .. } => Some(imported.clone()),
        _ => None,
      };

      let module = match &sym_data.origin {
        sem_ts::SymbolOrigin::Import { from, .. } => match from {
          sem_ts::ModuleRef::File(file) => Some(*file),
          _ => None,
        },
        _ => match &sym_data.owner {
          sem_ts::SymbolOwner::Module(file) => Some(*file),
          _ => None,
        },
      };

      let resolve_export_path = |mut module: sem_ts::FileId,
                                 segments: &[String],
                                 final_ns: sem_ts::Namespace|
       -> Option<DefId> {
        for (idx, segment) in segments.iter().enumerate() {
          let is_last = idx + 1 == segments.len();
          let ns = if is_last {
            final_ns
          } else {
            sem_ts::Namespace::NAMESPACE
          };
          let symbol = semantics.resolve_export(module, segment, ns)?;
          if is_last {
            return pick_def(symbol, final_ns)
              .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
              .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
          }
          match &semantics.symbols().symbol(symbol).origin {
            sem_ts::SymbolOrigin::Import { from, .. } => match from {
              sem_ts::ModuleRef::File(file) => module = *file,
              _ => return None,
            },
            _ => return None,
          }
        }
        None
      };

      let Some(origin) = module else {
        // Fall back to parent/member links when we can't resolve to a module export (e.g. global
        // `namespace` declarations that live outside of module graphs).
        let mut current = pick_def(symbol, sem_ts::Namespace::NAMESPACE)
          .or_else(|| pick_def(symbol, final_ns))
          .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE))?;
        for (idx, segment) in path.iter().enumerate().skip(1) {
          let is_last = idx + 1 == path.len();
          let ns = if is_last {
            final_ns
          } else {
            sem_ts::Namespace::NAMESPACE
          };
          current = *self
            .qualified_def_members
            .get(&(current, segment.clone(), ns))?;
        }
        return Some(current);
      };

      if let Some(def) = resolve_export_path(origin, &path[1..], final_ns) {
        return Some(def);
      }

      // Named imports of a namespace export (e.g. `import { ns } from "./mod"; import Foo = ns.Bar`)
      // need to hop through the imported export name.
      let Some(imported_name) = imported_name else {
        return None;
      };
      if imported_name == "*" {
        return None;
      }
      let mut segments = Vec::with_capacity(path.len());
      segments.push(imported_name);
      segments.extend_from_slice(&path[1..]);
      resolve_export_path(origin, &segments, final_ns)
    };

    if let Some(def) = resolve_via_semantics() {
      return Some(def);
    }
    if path.is_empty() {
      return None;
    }
    let lowered = self.hir_lowered.get(&file)?;
    let start_ns = if path.len() == 1 {
      final_ns
    } else {
      sem_ts::Namespace::NAMESPACE
    };
    let mut current: Option<DefId> = None;
    let mut best_pri = u8::MAX;
    for def in lowered.defs.iter() {
      if def.parent.is_some() {
        continue;
      }
      let Some(name) = lowered.names.resolve(def.name) else {
        continue;
      };
      if name != path[0].as_str() {
        continue;
      }
      let pri = self.def_priority(def.id, start_ns);
      if pri == u8::MAX {
        continue;
      }
      let replace = current
        .map(|best| pri < best_pri || (pri == best_pri && def.id < best))
        .unwrap_or(true);
      if replace {
        current = Some(def.id);
        best_pri = pri;
      }
    }
    let mut current = current.or_else(|| {
      let def = self
        .files
        .get(&file)?
        .bindings
        .get(&path[0])
        .and_then(|binding| binding.def)?;
      (self.def_priority(def, start_ns) != u8::MAX).then_some(def)
    })?;
    if path.len() == 1 {
      return Some(current);
    }
    for (idx, segment) in path.iter().enumerate().skip(1) {
      let is_last = idx + 1 == path.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let current_def = lowered.def(current)?;
      let hir_js::DefTypeInfo::Namespace { members } = current_def.type_info.as_ref()? else {
        return None;
      };
      let mut candidates: Vec<DefId> = Vec::new();
      for member_def in members.iter().copied() {
        let Some(member) = lowered.def(member_def) else {
          continue;
        };
        let Some(name) = lowered.names.resolve(member.name) else {
          continue;
        };
        if name == segment.as_str() {
          candidates.push(member_def);
        }
      }
      let mut best: Option<(u8, DefId)> = None;
      for def in candidates {
        let pri = self.def_priority(def, ns);
        if pri == u8::MAX {
          continue;
        }
        best = match best {
          Some((best_pri, best_def)) if best_pri < pri || (best_pri == pri && best_def <= def) => {
            Some((best_pri, best_def))
          }
          _ => Some((pri, def)),
        };
      }
      current = best.map(|(_, def)| def)?;
    }
    Some(current)
  }

  fn resolve_import_alias_target(&self, file: FileId, path: &[String]) -> Option<DefId> {
    self
      .resolve_import_alias_target_in_namespace(file, path, sem_ts::Namespace::VALUE)
      .or_else(|| {
        self.resolve_import_alias_target_in_namespace(file, path, sem_ts::Namespace::TYPE)
      })
      .or_else(|| {
        self.resolve_import_alias_target_in_namespace(file, path, sem_ts::Namespace::NAMESPACE)
      })
  }

  fn resolve_ambient_import_alias_target_in_namespace(
    &self,
    specifier: &str,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let semantics = self.semantics.as_ref()?;
    if path.is_empty() {
      return None;
    }

    let module_symbols = semantics.ambient_module_symbols().get(specifier)?;
    let group = module_symbols.get(&path[0])?;
    let symbol = group
      .symbol_for(sem_ts::Namespace::NAMESPACE, semantics.symbols())
      .or_else(|| group.symbol_for(final_ns, semantics.symbols()))
      .or_else(|| group.symbol_for(sem_ts::Namespace::VALUE, semantics.symbols()))?;

    let pick_def = |symbol: sem_ts::SymbolId, ns: sem_ts::Namespace| -> Option<DefId> {
      let symbols = semantics.symbols();
      let mut best: Option<(u8, usize, DefId)> = None;
      for (idx, decl_id) in semantics.symbol_decls(symbol, ns).iter().enumerate() {
        let decl = symbols.decl(*decl_id);
        let Some(def) = self.map_decl_to_program_def(decl, ns) else {
          continue;
        };
        let pri = self.def_priority(def, ns);
        if pri == u8::MAX {
          continue;
        }
        let key = (pri, idx, def);
        best = match best {
          Some((best_pri, best_idx, best_def)) if (best_pri, best_idx, best_def) <= key => {
            Some((best_pri, best_idx, best_def))
          }
          _ => Some(key),
        };
      }
      best.map(|(_, _, def)| def)
    };

    if path.len() == 1 {
      return pick_def(symbol, final_ns)
        .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
        .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
    }

    let sym_data = semantics.symbols().symbol(symbol);
    let imported_name = match &sym_data.origin {
      sem_ts::SymbolOrigin::Import { imported, .. } => Some(imported.clone()),
      _ => None,
    };
    let module_ref = match &sym_data.origin {
      sem_ts::SymbolOrigin::Import { from, .. } => Some(from.clone()),
      _ => None,
    };

    let resolve_export_path = |mut module: sem_ts::ModuleRef,
                               segments: &[String],
                               final_ns: sem_ts::Namespace|
     -> Option<DefId> {
      for (idx, segment) in segments.iter().enumerate() {
        let is_last = idx + 1 == segments.len();
        let ns = if is_last {
          final_ns
        } else {
          sem_ts::Namespace::NAMESPACE
        };
        let symbol = match &module {
          sem_ts::ModuleRef::File(file) => semantics.resolve_export(*file, segment, ns)?,
          sem_ts::ModuleRef::Ambient(spec) => semantics
            .exports_of_ambient_module(spec)?
            .get(segment)?
            .symbol_for(ns, semantics.symbols())?,
          sem_ts::ModuleRef::Unresolved(_) => return None,
        };
        if is_last {
          return pick_def(symbol, final_ns)
            .or_else(|| pick_def(symbol, sem_ts::Namespace::NAMESPACE))
            .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE));
        }
        module = match &semantics.symbols().symbol(symbol).origin {
          sem_ts::SymbolOrigin::Import { from, .. } => from.clone(),
          _ => return None,
        };
      }
      None
    };

    let Some(origin) = module_ref else {
      let mut current = pick_def(symbol, sem_ts::Namespace::NAMESPACE)
        .or_else(|| pick_def(symbol, final_ns))
        .or_else(|| pick_def(symbol, sem_ts::Namespace::VALUE))?;
      for (idx, segment) in path.iter().enumerate().skip(1) {
        let is_last = idx + 1 == path.len();
        let ns = if is_last {
          final_ns
        } else {
          sem_ts::Namespace::NAMESPACE
        };
        current = *self
          .qualified_def_members
          .get(&(current, segment.clone(), ns))?;
      }
      return Some(current);
    };

    if let Some(def) = resolve_export_path(origin.clone(), &path[1..], final_ns) {
      return Some(def);
    }

    let Some(imported_name) = imported_name else {
      return None;
    };
    if imported_name == "*" {
      return None;
    }
    let mut segments = Vec::with_capacity(path.len());
    segments.push(imported_name);
    segments.extend_from_slice(&path[1..]);
    resolve_export_path(origin, &segments, final_ns)
  }

  fn resolve_ambient_import_alias_target(&self, specifier: &str, path: &[String]) -> Option<DefId> {
    self
      .resolve_ambient_import_alias_target_in_namespace(specifier, path, sem_ts::Namespace::VALUE)
      .or_else(|| {
        self.resolve_ambient_import_alias_target_in_namespace(
          specifier,
          path,
          sem_ts::Namespace::TYPE,
        )
      })
      .or_else(|| {
        self.resolve_ambient_import_alias_target_in_namespace(
          specifier,
          path,
          sem_ts::Namespace::NAMESPACE,
        )
      })
  }

  fn module_namespace_object_type(&mut self, exports: &ExportMap) -> Result<TypeId, FatalError> {
    if let Some(store) = self.interned_store.as_ref().cloned() {
      let mut shape = tti::Shape::new();
      for (name, entry) in exports.iter() {
        if name == "*" {
          continue;
        }
        let resolved_def = entry
          .def
          .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
        if let Some(def) = resolved_def {
          if let Some(data) = self.def_data.get(&def) {
            if matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)) {
              continue;
            }
          }
        }
        let mut ty = entry.type_id;
        if ty.is_none() {
          if let Some(def) = resolved_def {
            ty = self.export_type_for_def(def)?;
            if ty.is_none() {
              ty = Some(self.type_of_def(def)?);
            }
          }
        }
        let ty = ty.unwrap_or(self.builtin.unknown);
        let ty = self.ensure_interned_type(ty);
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      Ok(store.intern_type(tti::TypeKind::Object(obj_id)))
    } else {
      let mut obj = ObjectType::empty();
      for (name, entry) in exports.iter() {
        if name == "*" {
          continue;
        }
        let resolved_def = entry
          .def
          .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
        if let Some(def) = resolved_def {
          if let Some(data) = self.def_data.get(&def) {
            if matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)) {
              continue;
            }
          }
        }
        let mut ty = entry.type_id;
        if ty.is_none() {
          if let Some(def) = resolved_def {
            ty = self.export_type_for_def(def)?;
            if ty.is_none() {
              ty = Some(self.type_of_def(def)?);
            }
          }
        }
        let ty = ty.unwrap_or(self.builtin.unknown);
        obj.props.insert(
          name.clone(),
          ObjectProperty {
            typ: ty,
            optional: false,
            readonly: true,
          },
        );
      }
      Ok(self.type_store.object(obj))
    }
  }

  fn module_namespace_type(&mut self, file: FileId) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let store = match self.interned_store.as_ref() {
      Some(store) => Arc::clone(store),
      None => {
        let store = tti::TypeStore::with_options((&self.compiler_options).into());
        self.interned_store = Some(Arc::clone(&store));
        store
      }
    };

    if let Some(cached) = self.module_namespace_types.get(&file).copied() {
      return Ok(cached);
    }

    let prim = store.primitive_ids();
    if self.module_namespace_in_progress.contains(&file) {
      return Ok(prim.unknown);
    }

    self.module_namespace_in_progress.insert(file);
    let computed = panic::catch_unwind(AssertUnwindSafe(|| {
      let exports = self.exports_of_file(file)?;
      let mut names: Vec<String> = if let Some(semantics) = self.semantics.as_ref() {
        semantics
          .exports_of_opt(sem_ts::FileId(file.0))
          .map(|exports| {
            exports
              .iter()
              .filter_map(|(name, group)| {
                group
                  .symbol_for(sem_ts::Namespace::VALUE, semantics.symbols())
                  .is_some()
                  .then_some(name.clone())
              })
              .collect()
          })
          .unwrap_or_default()
      } else {
        exports
          .iter()
          .filter_map(|(name, entry)| {
            let is_value = entry
              .def
              .and_then(|def| self.def_data.get(&def))
              .map(|data| !matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)))
              .unwrap_or(true);
            is_value.then_some(name.clone())
          })
          .collect()
      };
      names.sort();
      names.dedup();

      let mut shape = tti::Shape::new();
      let mut cache = HashMap::new();
      for name in names.into_iter() {
        let entry = exports.get(&name);
        let ty = entry
          .and_then(|entry| entry.type_id)
          .or_else(|| {
            entry
              .and_then(|entry| entry.def)
              .and_then(|def| self.export_type_for_def(def).ok().flatten())
          })
          .or_else(|| {
            entry
              .and_then(|entry| entry.def)
              .and_then(|def| self.def_types.get(&def).copied())
          })
          .unwrap_or(prim.unknown);
        let ty = if store.contains_type_id(ty) {
          store.canon(ty)
        } else {
          store.canon(convert_type_for_display(ty, self, &store, &mut cache))
        };
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      Ok(store.canon(store.intern_type(tti::TypeKind::Object(obj_id))))
    }));
    self.module_namespace_in_progress.remove(&file);
    let ty = match computed {
      Ok(Ok(ty)) => ty,
      Ok(Err(err)) => return Err(err),
      Err(payload) => panic::resume_unwind(payload),
    };
    self.module_namespace_types.insert(file, ty);
    Ok(ty)
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

  fn object_type_from_members(&mut self, members: &[Node<TypeMember>]) -> ObjectType {
    let mut object = ObjectType::empty();
    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some(name) = type_member_name(&prop.stx.key) {
            let ty = prop
              .stx
              .type_annotation
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
              .unwrap_or(self.builtin.unknown);
            object.props.insert(
              name,
              ObjectProperty {
                typ: ty,
                optional: prop.stx.optional,
                readonly: prop.stx.readonly,
              },
            );
          }
        }
        TypeMember::Method(method) => {
          if let Some(name) = type_member_name(&method.stx.key) {
            let params = method
              .stx
              .parameters
              .iter()
              .map(|p| self.type_from_type_expr(&p.stx.type_expr))
              .collect();
            let ret = method
              .stx
              .return_type
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
              .unwrap_or(self.builtin.unknown);
            let func_ty = self.type_store.function(params, ret);
            object.props.insert(
              name,
              ObjectProperty {
                typ: func_ty,
                optional: method.stx.optional,
                readonly: false,
              },
            );
          }
        }
        TypeMember::IndexSignature(index) => {
          let value = self.type_from_type_expr(&index.stx.type_annotation);
          let param_type = self.type_from_type_expr(&index.stx.parameter_type);
          let param_kind = self.type_store.kind(param_type).clone();
          match param_kind {
            TypeKind::Number => object.number_index = Some(value),
            TypeKind::String => object.string_index = Some(value),
            _ => object.string_index = Some(value),
          }
        }
        _ => {}
      }
    }
    object
  }

  fn merge_object_types(&mut self, mut base: ObjectType, extra: ObjectType) -> ObjectType {
    for (name, prop) in extra.props.into_iter() {
      match base.props.entry(name) {
        Entry::Vacant(entry) => {
          entry.insert(prop);
        }
        Entry::Occupied(mut entry) => {
          let existing = entry.get_mut();
          existing.typ = self
            .type_store
            .union(vec![existing.typ, prop.typ], &self.builtin);
          existing.optional = existing.optional || prop.optional;
          existing.readonly = existing.readonly || prop.readonly;
        }
      }
    }

    if base.string_index.is_none() {
      base.string_index = extra.string_index;
    }
    if base.number_index.is_none() {
      base.number_index = extra.number_index;
    }

    base
  }

  fn type_from_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
      TypeExpr::TypeReference(reference) => {
        if let Some(file) = self.current_file {
          let span = loc_to_span(file, reference.loc).range;
          let mut segments = Vec::new();
          fn collect_segments(name: &TypeEntityName, out: &mut Vec<String>) {
            match name {
              TypeEntityName::Identifier(id) => out.push(id.clone()),
              TypeEntityName::Qualified(qn) => {
                collect_segments(&qn.left, out);
                out.push(qn.right.clone());
              }
              TypeEntityName::Import(_) => {}
            }
          }
          collect_segments(&reference.stx.name, &mut segments);
          let mut binding_defs = HashMap::new();
          if let Some(state) = self.files.get(&file) {
            for (name, binding) in state.bindings.iter() {
              if let Some(def) = binding.def {
                binding_defs.insert(name.clone(), def);
              }
            }
          }

          let mut resolved_def = None;
          if !binding_defs.is_empty() {
            if let Some(resolver) = self.build_type_resolver(&binding_defs) {
              resolved_def = resolver.resolve_type_name(&segments);
            }
          }

          if resolved_def.is_none() {
            if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
              let mut entries: Vec<_> = self.def_data.iter().collect();
              entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
              let mut best: Option<(DefId, u8)> = None;
              for (id, data) in entries.into_iter() {
                if data.name != *type_name {
                  continue;
                }
                let pri = self.def_priority(*id, sem_ts::Namespace::TYPE);
                match best {
                  Some((_, existing)) if existing <= pri => {}
                  _ => best = Some((*id, pri)),
                }
              }
              if let Some((id, _)) = best {
                resolved_def = Some(id);
              }
            }
          }

          if let Some(def) = resolved_def {
            if let Some(symbol) = self.def_data.get(&def).map(|d| d.symbol) {
              self.record_symbol(file, span, symbol);
            }
            if let Err(fatal) = self.type_of_def(def) {
              if !matches!(fatal, FatalError::Cancelled) {
                self.diagnostics.push(fatal_to_diagnostic(fatal));
              }
              return self.builtin.unknown;
            }
            if let Some(store) = self.interned_store.as_ref() {
              if let Some(ty) = self.interned_def_types.get(&def).copied() {
                let ty = store.canon(ty);
                if !matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
                  return ty;
                }
              }
            }
            return self
              .def_types
              .get(&def)
              .copied()
              .unwrap_or(self.builtin.unknown);
          }
        }
        self.builtin.unknown
      }
      TypeExpr::Object(_) => self.builtin.object,
      TypeExpr::Number(_) => self.builtin.number,
      TypeExpr::String(_) => self.builtin.string,
      TypeExpr::Boolean(_) => self.builtin.boolean,
      TypeExpr::Any(_) => self.builtin.any,
      TypeExpr::Unknown(_) => self.builtin.unknown,
      TypeExpr::Null(_) => self.builtin.null,
      TypeExpr::Undefined(_) => self.builtin.undefined,
      TypeExpr::Void(_) => self.builtin.void,
      TypeExpr::Never(_) => self.builtin.never,
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.type_from_type_expr(t)).collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeExpr::TupleType(tuple) => {
        let readonly = tuple.stx.readonly;
        let elements = tuple
          .stx
          .elements
          .iter()
          .map(|elem| self.type_from_type_expr(&elem.stx.type_expr))
          .collect();
        self.type_store.tuple(elements, readonly)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(element_type);
        self.type_store.array(elem)
      }
      TypeExpr::FunctionType(func) => {
        let params = func
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&func.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ConstructorType(cons) => {
        let params = cons
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&cons.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ObjectType(obj) => {
        let object = self.object_type_from_members(&obj.stx.members);
        self.type_store.object(object)
      }
      TypeExpr::MappedType(mapped) => {
        let source = self.type_from_type_expr(&mapped.stx.constraint);
        let value = self.type_from_type_expr(&mapped.stx.type_expr);
        self.type_store.mapped(source, value)
      }
      TypeExpr::ParenthesizedType(inner) => self.type_from_type_expr(&inner.stx.type_expr),
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::Boolean(value) => self.type_store.literal_boolean(*value),
        TypeLiteral::Number(n) => self.type_store.literal_number(n.clone()),
        TypeLiteral::String(s) => self.type_store.literal_string(s.clone()),
        TypeLiteral::Null => self.builtin.null,
        _ => self.builtin.unknown,
      },
      TypeExpr::TypePredicate(pred) => {
        let asserted = pred
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t));
        self
          .type_store
          .predicate(pred.stx.parameter_name.clone(), asserted, pred.stx.asserts)
      }
      TypeExpr::TypeQuery(query) => {
        fn entity_name_segments(name: &TypeEntityName) -> Option<Vec<String>> {
          match name {
            TypeEntityName::Identifier(id) => Some(vec![id.clone()]),
            TypeEntityName::Qualified(qualified) => {
              let mut parts = entity_name_segments(&qualified.left)?;
              parts.push(qualified.right.clone());
              Some(parts)
            }
            TypeEntityName::Import(_) => None,
          }
        }

        if let Some(path) = entity_name_segments(&query.stx.expr_name) {
          let mut binding_defs = HashMap::new();
          let mut local_binding = None;
          if let Some(file) = self.current_file {
            if let Some(state) = self.files.get(&file) {
              for (name, binding) in state.bindings.iter() {
                if let Some(def) = binding.def {
                  binding_defs.insert(name.clone(), def);
                }
              }
              if path.len() == 1 {
                local_binding = state.bindings.get(&path[0]).cloned();
              }
            }
          }
          if let Some(binding) = local_binding {
            if let Some(file) = self.current_file {
              self.record_symbol(file, loc_to_span(file, query.loc).range, binding.symbol);
            }
            let mut ty = None;
            if let Some(def) = binding.def {
              if let Some(DefKind::Import(import)) = self.def_data.get(&def).map(|d| d.kind.clone())
              {
                if let Ok(exports) = self.exports_for_import(&import) {
                  if let Some(entry) = exports.get(&import.original) {
                    let mut mapped = None;
                    if let Some(target_def) = entry.def {
                      if let Ok(Some(exported)) = self.export_type_for_def(target_def) {
                        mapped = Some(exported);
                      } else if let Ok(found) = self.type_of_def(target_def) {
                        mapped = Some(found);
                      }
                    }
                    if mapped.is_none() {
                      mapped = entry.type_id;
                    }
                    if let Some(mapped) = mapped {
                      let mapped = match self.resolve_value_ref_type(mapped) {
                        Ok(resolved) => resolved,
                        Err(FatalError::Cancelled) => return self.builtin.unknown,
                        Err(fatal) => {
                          self.diagnostics.push(fatal_to_diagnostic(fatal));
                          self.builtin.unknown
                        }
                      };
                      if mapped != self.builtin.unknown {
                        return mapped;
                      }
                    }
                  }
                }
              }
              match self.type_of_def(def) {
                Ok(found) => ty = Some(found),
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  return self.builtin.unknown;
                }
              }
            }
            if ty.is_none() {
              ty = binding.type_id;
            }
            if let Some(ty) = ty {
              let ty = match self.resolve_value_ref_type(ty) {
                Ok(resolved) => resolved,
                Err(FatalError::Cancelled) => return self.builtin.unknown,
                Err(fatal) => {
                  self.diagnostics.push(fatal_to_diagnostic(fatal));
                  self.builtin.unknown
                }
              };
              if ty != self.builtin.unknown {
                return ty;
              }
            }
          }
          if let Some(resolver) = self.build_type_resolver(&binding_defs) {
            if let Some(def) = resolver.resolve_typeof(&path) {
              return match self.type_of_def(def) {
                Ok(ty) => match self.resolve_value_ref_type(ty) {
                  Ok(resolved) => resolved,
                  Err(FatalError::Cancelled) => self.builtin.unknown,
                  Err(fatal) => {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                    self.builtin.unknown
                  }
                },
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  self.builtin.unknown
                }
              };
            }
          }
          if path.len() == 1 {
            let mut entries: Vec<_> = self.def_data.iter().collect();
            entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
            let mut best: Option<(DefId, u8)> = None;
            for (id, data) in entries.into_iter() {
              if data.name != path[0] {
                continue;
              }
              let pri = self.def_priority(*id, sem_ts::Namespace::VALUE);
              match best {
                Some((_, existing)) if existing <= pri => {}
                _ => best = Some((*id, pri)),
              }
            }
            if let Some((id, _)) = best {
              return match self.type_of_def(id) {
                Ok(ty) => match self.resolve_value_ref_type(ty) {
                  Ok(resolved) => resolved,
                  Err(FatalError::Cancelled) => self.builtin.unknown,
                  Err(fatal) => {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                    self.builtin.unknown
                  }
                },
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  self.builtin.unknown
                }
              };
            }
          }
        }

        self.builtin.unknown
      }
      _ => self.builtin.unknown,
    }
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
