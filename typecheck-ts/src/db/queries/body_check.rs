//! Salsa-first body checking.
//!
//! `check_body_tracked` is the *only* final-grade body checker in the crate: a
//! salsa tracked function over
//!
//! - the per-file derived queries `parse`/`lower_hir` (so an edit to one file
//!   only dirties that file's bodies), and
//! - the program-wide [`BodyCheckContext`] input (interned declaration types,
//!   bindings, exports, semantics), whose *semantic* equality lets salsa
//!   backdate dependents when a rebuild after an edit produces an equivalent
//!   environment.
//!
//! The context is built by `ProgramState` (the imperative declaration-types
//! layer, still outside salsa — see `wiki/status/roadmap.md` § structural
//! refactors) and written into the database via
//! [`Database::set_body_context`](crate::db::Database::set_body_context).
//! Body checking itself, and everything downstream of it
//! (`program_diagnostics`, `type_at`, span queries), runs through salsa's
//! dependency tracking; there is no result seeding.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::panic::panic_any;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};
use std::time::Instant;

use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{Body as HirBody, BodyId as HirBodyId, BodyKind as HirBodyKind, NameInterner};
use hir_js::{PatId as HirPatId, PatKind as HirPatKind};
use semantic_js::ts as sem_ts;
use types_ts_interned::{
  IntrinsicKind, RelateCtx, TypeId as InternedTypeId, TypeKind, TypeParamDecl, TypeParamId,
  TypeStore,
};

use crate::check::caches::{CheckerCacheStats, CheckerCaches};
use crate::check::hir_body::{
  build_private_in_targets, check_body_with_env_with_bindings, check_body_with_expander,
  type_id_is_da_exempt, BindingTypeResolver, DaTypeAliasMap,
};
use crate::codes;
use crate::db::expander::{DbTypeExpander, TypeExpanderDb};
use crate::db::queries::{lower_hir_for, parse_for};
use crate::db::Db;
use crate::files::FileRegistry;
use crate::lib_support::{CacheMode, CacheOptions, JsxMode, ScriptTarget};
use crate::profile::{QueryKind, QueryStatsCollector};
use crate::program::check::relate_hooks;
use crate::program::{NamespaceMemberIndex, ProgramTypeResolver};
use crate::{BodyCheckResult, BodyId, DefId, ExportMap, Host, PatId, SymbolBinding, TypeId};

/// Program-wide semantic environment consumed by body checking.
///
/// Deliberately contains *no per-file syntax artifacts* (ASTs, lowered HIR):
/// those are read through the per-file salsa queries so that invalidation
/// stays file-granular. Everything in here is program-wide and changes only
/// when declaration-grade facts change.
#[derive(Clone)]
pub struct BodyCheckContext {
  pub store: Arc<TypeStore>,
  pub target: ScriptTarget,
  pub no_implicit_any: bool,
  pub use_define_for_class_fields: bool,
  pub strict_null_checks: bool,
  pub strict_property_initialization: bool,
  pub interned_def_types: HashMap<DefId, InternedTypeId>,
  /// Class/enum type-def → synthetic value-def (constructor side). Value
  /// bindings must map through this before reading `interned_def_types`,
  /// which stores the *instance* type under the class def.
  pub value_defs: Arc<HashMap<DefId, DefId>>,
  pub interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
  pub interned_type_param_decls: HashMap<DefId, Arc<[TypeParamDecl]>>,
  pub interned_intrinsics: HashMap<DefId, IntrinsicKind>,
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
  /// JS expando members (outer var def → member names) registered from
  /// `Outer.X = …` special assignments. Used to skip the assignability check
  /// at the binding site (tsc derives the member type from the RHS).
  pub expando_members: Arc<HashMap<DefId, HashSet<String>>>,
  pub(crate) file_registry: Arc<FileRegistry>,
  pub host: Arc<dyn Host>,
  pub checker_caches: CheckerCaches,
  pub cache_mode: CacheMode,
  pub cache_options: CacheOptions,
  pub jsx_mode: Option<JsxMode>,
  pub query_stats: QueryStatsCollector,
  /// Shared accumulator for per-body checker cache statistics
  /// ([`CacheMode::PerBody`] only). `ProgramState` drains this into its
  /// `cache_stats` so `Program::query_stats()` keeps reporting per-body cache
  /// behavior. Instrumentation only; excluded from equality.
  pub cache_stats_sink: Arc<Mutex<CheckerCacheStats>>,
  pub cancelled: Arc<AtomicBool>,
}

/// Semantic equality: two contexts are equal when body checking against them
/// must produce identical results.
///
/// This equality is the backdating firewall for `check_body_tracked`: after an
/// edit, `ProgramState` rebuilds the context and rewrites the input; if the
/// rebuilt value compares equal here, salsa backdates and unaffected bodies
/// are not re-checked. Getting a field's treatment wrong is therefore a
/// *correctness* bug (stale results), not a performance bug — when in doubt,
/// compare by content.
///
/// - `store`, `semantics`, `host`: `Arc` pointer identity. The store `Arc` is
///   retained for the lifetime of a `Program` (swapped only when compiler
///   options change), and `semantics` comes from the salsa `ts_semantics`
///   query which backdates per-file (so an unchanged program keeps the same
///   `Arc` across re-analysis). `host` is fixed at `Program` construction.
/// - Interned type tables compare by content. `TypeId`s are content-addressed
///   in the (pointer-identical) store, so recomputation of unchanged
///   declarations yields identical ids.
/// - `checker_caches`, `query_stats`, `cancelled` are performance /
///   instrumentation / control channels that never influence checked output;
///   they are deliberately excluded.
impl BodyCheckContext {
  /// Debug helper: report which fields differ (used when
  /// `DEBUG_BODY_CTX_EQ` is set to explain a failed backdate).
  fn debug_diff(&self, other: &Self) {
    let mut diffs: Vec<&str> = Vec::new();
    if !Arc::ptr_eq(&self.store, &other.store) {
      diffs.push("store(ptr)");
    }
    match (&self.semantics, &other.semantics) {
      (Some(a), Some(b)) if !Arc::ptr_eq(a, b) => diffs.push("semantics(ptr)"),
      (None, Some(_)) | (Some(_), None) => diffs.push("semantics(present)"),
      _ => {}
    }
    if !Arc::ptr_eq(&self.host, &other.host) {
      diffs.push("host(ptr)");
    }
    macro_rules! cmp {
      ($field:ident) => {
        if self.$field != other.$field {
          diffs.push(stringify!($field));
        }
      };
    }
    cmp!(target);
    cmp!(no_implicit_any);
    cmp!(use_define_for_class_fields);
    cmp!(strict_null_checks);
    cmp!(strict_property_initialization);
    cmp!(jsx_mode);
    cmp!(cache_mode);
    cmp!(cache_options);
    cmp!(interned_def_types);
    cmp!(interned_type_params);
    cmp!(interned_type_param_decls);
    cmp!(interned_intrinsics);
    cmp!(body_info);
    cmp!(body_parents);
    cmp!(global_bindings);
    cmp!(file_bindings);
    cmp!(def_spans);
    cmp!(def_kinds);
    cmp!(def_files);
    cmp!(def_id_spans);
    cmp!(exports);
    cmp!(module_namespace_defs);
    cmp!(namespace_members);
    cmp!(qualified_def_members);
    cmp!(expando_members);
    cmp!(file_registry);
    eprintln!("BodyCheckContext eq: differing fields: {diffs:?}");
    if self.def_spans != other.def_spans {
      for (key, def) in self.def_spans.iter() {
        match other.def_spans.get(key) {
          Some(other_def) if other_def == def => {}
          Some(other_def) => {
            let kind_a = self.def_kinds.get(def).map(std::mem::discriminant);
            let kind_b = other.def_kinds.get(other_def).map(std::mem::discriminant);
            eprintln!(
              "  def_spans {key:?}: {def:?} (local {:#x}, {kind_a:?}) vs {other_def:?} (local {:#x}, {kind_b:?})",
              def.0 & 0xFFFF_FFFF,
              other_def.0 & 0xFFFF_FFFF
            );
          }
          None => eprintln!("  def_spans {key:?}: {def:?} removed"),
        }
      }
      for (key, def) in other.def_spans.iter() {
        if !self.def_spans.contains_key(key) {
          eprintln!("  def_spans {key:?}: {def:?} added");
        }
      }
    }
  }
}

impl PartialEq for BodyCheckContext {
  fn eq(&self, other: &Self) -> bool {
    if std::env::var_os("DEBUG_BODY_CTX_EQ").is_some() {
      self.debug_diff(other);
    }
    Arc::ptr_eq(&self.store, &other.store)
      && self.target == other.target
      && self.no_implicit_any == other.no_implicit_any
      && self.use_define_for_class_fields == other.use_define_for_class_fields
      && self.strict_null_checks == other.strict_null_checks
      && self.strict_property_initialization == other.strict_property_initialization
      && self.jsx_mode == other.jsx_mode
      && self.cache_mode == other.cache_mode
      && self.cache_options == other.cache_options
      && match (&self.semantics, &other.semantics) {
        (Some(a), Some(b)) => Arc::ptr_eq(a, b),
        (None, None) => true,
        _ => false,
      }
      && Arc::ptr_eq(&self.host, &other.host)
      && self.interned_def_types == other.interned_def_types
      && self.value_defs == other.value_defs
      && self.interned_type_params == other.interned_type_params
      && self.interned_type_param_decls == other.interned_type_param_decls
      && self.interned_intrinsics == other.interned_intrinsics
      && self.body_info == other.body_info
      && self.body_parents == other.body_parents
      && self.global_bindings == other.global_bindings
      && self.file_bindings == other.file_bindings
      && self.def_spans == other.def_spans
      && self.def_kinds == other.def_kinds
      && self.def_files == other.def_files
      && self.def_id_spans == other.def_id_spans
      && self.exports == other.exports
      && self.module_namespace_defs == other.module_namespace_defs
      && self.namespace_members == other.namespace_members
      && self.qualified_def_members == other.qualified_def_members
      && self.expando_members == other.expando_members
      && self.file_registry == other.file_registry
  }
}

impl Eq for BodyCheckContext {}

impl fmt::Debug for BodyCheckContext {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("BodyCheckContext")
      .field("defs", &self.interned_def_types.len())
      .field("bodies", &self.body_info.len())
      .finish()
  }
}

/// Salsa-storable handle for the shared body-check context.
#[derive(Clone, Debug)]
pub struct BodyContextHandle(pub Arc<BodyCheckContext>);

impl PartialEq for BodyContextHandle {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.0, &other.0) || self.0.as_ref() == other.0.as_ref()
  }
}

impl Eq for BodyContextHandle {}

unsafe impl salsa::Update for BodyContextHandle {
  unsafe fn maybe_update(old_pointer: *mut Self, new_value: Self) -> bool {
    let old_value = &mut *old_pointer;
    if *old_value == new_value {
      false
    } else {
      *old_value = new_value;
      true
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BodyInfo {
  pub file: FileId,
  pub hir: Option<HirBodyId>,
  pub kind: HirBodyKind,
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
  static LOCAL_TRACKER: std::cell::RefCell<Option<Arc<ParallelTracker>>> =
    std::cell::RefCell::new(None);
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

  fn is_enum_type(&self, def: types_ts_interned::DefId) -> bool {
    matches!(
      self.def_kinds.get(&crate::api::DefId(def.0)),
      Some(crate::DefKind::Enum(_))
    )
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
    yield_types: Vec::new(),
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
    yield_types: Vec::new(),
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
    yield_types: Vec::new(),
  }
}

/// Backdating firewall between the context *input* and body checks.
///
/// Setting an input always moves salsa to a new revision; this tracked wrapper
/// re-reads the input (cheap) and produces a value whose [`PartialEq`] is the
/// semantic equality defined on [`BodyCheckContext`]. When `ProgramState`
/// republishes an equivalent environment after an edit, this query's output
/// compares equal, salsa backdates it, and memoized `check_body_tracked`
/// results for untouched files stay valid.
#[salsa::tracked]
fn body_context_tracked(db: &dyn Db) -> Option<BodyContextHandle> {
  db.body_context_input().context(db)
}

/// Check a single body. This is the public entry point; results are memoized
/// by salsa and shared across threads (concurrent callers of the same body
/// block on the first computation instead of duplicating it).
pub fn check_body(db: &dyn Db, body: BodyId) -> Arc<BodyCheckResult> {
  check_body_tracked(db, body, ())
}

// The unit seed mirrors `decl_types_in_file`: with a second argument salsa
// auto-interns the key tuple, so `BodyId` does not need to be a salsa struct.
#[salsa::tracked(recovery_fn = check_body_recover)]
fn check_body_tracked(db: &dyn Db, body: BodyId, _seed: ()) -> Arc<BodyCheckResult> {
  let Some(handle) = body_context_tracked(db) else {
    // No context published yet (database used directly, or analysis has not
    // run). Mirror the pre-salsa behavior of "no cached result": an empty
    // result, which downstream consumers treat as absence.
    return Arc::new(empty_result(body));
  };
  db.record_body_check();
  compute_body(db, &handle.0, body)
}

fn check_body_recover(
  db: &dyn Db,
  _cycle: &salsa::Cycle,
  body: BodyId,
  _seed: (),
) -> Arc<BodyCheckResult> {
  // A body-parent cycle would be a corrupt `body_parents` table; recover with
  // an empty result (the imperative checker returned the same for re-entrant
  // checks) instead of panicking.
  let _ = db;
  Arc::new(empty_result(body))
}

fn compute_body(db: &dyn Db, ctx: &BodyCheckContext, body_id: BodyId) -> Arc<BodyCheckResult> {
  if ctx.cancelled.load(Ordering::Relaxed) {
    panic_any(crate::FatalError::Cancelled);
  }
  let started = Instant::now();
  let Some(meta) = ctx.body_info.get(&body_id).copied() else {
    return Arc::new(missing_body(body_id));
  };
  // Unseeded files behave like the pre-salsa context's "no AST/HIR snapshot".
  let Some(file_input) = db.file_input(meta.file) else {
    return Arc::new(empty_result(body_id));
  };
  let Some(lowered) = lower_hir_for(db, file_input).lowered else {
    return Arc::new(empty_result(body_id));
  };
  let parsed = parse_for(db, file_input);
  let Some(ast) = parsed.ast.as_ref() else {
    return Arc::new(missing_ast(body_id, meta.file));
  };

  let mut _synthetic = None;
  let body = if let Some(hir_id) = meta.hir {
    lowered.body(hir_id)
  } else if matches!(meta.kind, HirBodyKind::TopLevel) {
    _synthetic = Some(HirBody {
      owner: hir_js::ids::MISSING_DEF,
      span: TextRange::new(0, 0),
      kind: HirBodyKind::TopLevel,
      exprs: Vec::new(),
      stmts: Vec::new(),
      pats: Vec::new(),
      locals: Vec::new(),
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
    // Class/enum defs store the *instance* type; value bindings need the
    // constructor value stored under the synthetic value def (cross-file
    // ambient `declare class` + `new C(...)` in another file).
    let def = ctx.value_defs.get(&def).copied().unwrap_or(def);
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
    db,
    ctx,
    body_id,
    &mut bindings,
    &mut binding_defs,
    prim.unknown,
  );
  // Nested type-capable decls in this body (e.g. `constructor() { class
  // Derived { m(x: Derived) {} } }`). Parent bodies are seeded inside
  // `collect_parent_bindings`.
  {
    let mut seen: HashSet<String> = binding_defs.keys().cloned().collect();
    seed_type_decls_from_body(ctx, &lowered, body, &mut binding_defs, &mut seen, None);
  }
  // Heritage / `new C()` use value-namespace lookup. `seed_type_decls_*` only
  // fills the type resolver — also materialize class/enum ctor types.
  // Needed for namespace-nested siblings (`…CallSignatures4` `extends Base`).
  for (name, def) in binding_defs.iter() {
    if bindings.contains_key(name) {
      continue;
    }
    if !matches!(
      ctx.def_kinds.get(def),
      Some(crate::DefKind::Class(_) | crate::DefKind::Enum(_))
    ) {
      continue;
    }
    // The class def holds the *instance* type; the constructor value lives
    // under the synthetic value def.
    let def = ctx.value_defs.get(def).copied().unwrap_or(*def);
    let Some(ty) = ctx.interned_def_types.get(&def).copied() else {
      continue;
    };
    let ty = ctx.store.canon(ty);
    if matches!(ctx.store.type_kind(ty), TypeKind::Unknown) {
      continue;
    }
    bindings.insert(name.clone(), ty);
  }

  let caches = ctx.checker_caches.for_body();
  let expander = DbTypeExpander::new(ctx, caches.eval.clone());
  let contextual_fn_ty = if matches!(meta.kind, HirBodyKind::Function) {
    function_expr_span(db, ctx, body_id)
      .and_then(|span| contextual_callable_for_body(db, ctx, body_id, span))
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
  // The span→node index borrows from the memoized AST and is rebuilt per body
  // check; keeping it borrowed (no `'static` self-reference) is what lets the
  // index stay free of raw pointers.
  let ast_index =
    crate::check::hir_body::AstIndex::new(ast.as_ref(), meta.file, Some(&ctx.cancelled));
  // checkJs: scan leading JSDoc `@type` in `.js`/`.jsx` sources (parse-js does
  // not attach comments to AST nodes).
  let file_kind = crate::db::queries::file_kind(db, meta.file);
  let source_text = crate::db::queries::file_text(db, meta.file);
  let jsdoc_source = matches!(
    file_kind,
    crate::lib_support::FileKind::Js | crate::lib_support::FileKind::Jsx
  )
  .then_some(source_text.as_ref());
  let class_expr_value_tys = crate::check::hir_body::class_expr_value_types_for_body(
    body,
    &ctx.interned_def_types,
    ctx.store.as_ref(),
    None,
    Some(ctx.def_id_spans.as_ref()),
  );
  let mut result = check_body_with_expander(
    body_id,
    body,
    &lowered.names,
    meta.file,
    &ast_index,
    Arc::clone(&ctx.store),
    ctx.target,
    ctx.use_define_for_class_fields,
    ctx.strict_null_checks,
    ctx.strict_property_initialization,
    &caches,
    &bindings,
    resolver.clone(),
    Some(&expander),
    Some(&ctx.interned_type_param_decls),
    contextual_fn_ty,
    ctx.no_implicit_any,
    ctx.jsx_mode,
    Some(&ctx.cancelled),
    jsdoc_source,
    Some(&lowered.types),
    &class_expr_value_tys,
    &ctx.expando_members,
  );

  if !body.exprs.is_empty() && matches!(meta.kind, HirBodyKind::Function | HirBodyKind::TopLevel) {
    if ctx.cancelled.load(Ordering::Relaxed) {
      panic_any(crate::FatalError::Cancelled);
    }
    let mut initial_env: HashMap<_, _> = HashMap::new();
    // Prefer Body.locals / LocalId for parameter bindings.
    for (_local_id, local) in body.locals_with_kind(hir_js::LocalKind::Param) {
      let Some(pat_id) = local.pat else {
        continue;
      };
      if let Some(ty) = result.pat_types.get(pat_id.0 as usize).copied() {
        if ty != prim.unknown {
          initial_env.insert(local.name, ty);
        }
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
    flow_hooks.should_stop = Some(ctx.cancelled.as_ref());
    let flow_relate = RelateCtx::with_hooks_and_cache(
      Arc::clone(&ctx.store),
      ctx.store.options(),
      flow_hooks,
      caches.relation.clone(),
    );
    let mut pinned_foreign = Vec::new();
    let type_aliases =
      da_type_alias_map_for_file(db, ctx, meta.file, &lowered, &mut pinned_foreign);
    let private_in_targets = {
      let body_span = if body.span.start < body.span.end {
        body.span
      } else {
        TextRange::new(
          body.stmts.first().map(|s| s.span.start).unwrap_or(0),
          body.stmts.last().map(|s| s.span.end).unwrap_or(0),
        )
      };
      build_private_in_targets(&ast_index, body_span, |class_idx| {
        let name = ast_index.classes.get(class_idx)?.name.as_ref()?;
        let value_ty = *bindings.get(name)?;
        let instance = match ctx.store.type_kind(value_ty) {
          TypeKind::Object(obj_id) => {
            let shape = ctx.store.shape(ctx.store.object(obj_id).shape);
            shape
              .construct_signatures
              .first()
              .map(|sig| ctx.store.signature(*sig).ret)
          }
          TypeKind::Callable { overloads } => {
            overloads.first().map(|sig| ctx.store.signature(*sig).ret)
          }
          _ => None,
        }?;
        Some((instance, value_ty))
      })
    };
    let flow_result = check_body_with_env_with_bindings(
      body_id,
      body,
      &lowered.names,
      meta.file,
      "",
      Arc::clone(&ctx.store),
      &initial_env,
      None,
      flow_relate,
      Some(&expander),
      lowered.type_arenas(body.owner),
      Some(&type_aliases),
      private_in_targets,
      resolver.clone(),
      ctx.no_implicit_any,
    );
    let mut relate_hooks = relate_hooks();
    relate_hooks.expander = Some(&expander);
    relate_hooks.should_stop = Some(ctx.cancelled.as_ref());
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
    if let Ok(mut sink) = ctx.cache_stats_sink.lock() {
      sink.merge(&stats);
    }
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
  db: &dyn Db,
  ctx: &BodyCheckContext,
  body_id: BodyId,
  bindings: &mut HashMap<String, TypeId>,
  binding_defs: &mut HashMap<String, DefId>,
  unknown: TypeId,
) {
  let mut visited = HashSet::new();
  let mut seen_names = HashSet::new();
  // Span of the body being checked — used so top-level `namespace` blocks
  // (lowered as `StmtKind::Block`) only contribute decls when they enclose
  // this body, and those nested decls can shadow file-root same-named types
  // (`assignmentCompatWithNumericIndexer3.ts`: `namespace Generics { class A }`).
  let child_span = ctx.body_info.get(&body_id).and_then(|meta| {
    let hir_id = meta.hir?;
    let lowered = db
      .file_input(meta.file)
      .and_then(|input| lower_hir_for(db, input).lowered)?;
    lowered.body(hir_id).map(|b| b.span)
  });
  // Named class/function expression names bind inside their bodies (and
  // nested members). Seed nearest-first before outer pats so they shadow
  // captured parameters.
  seed_enclosing_named_exprs(
    db,
    ctx,
    body_id,
    bindings,
    binding_defs,
    &mut seen_names,
    unknown,
  );
  let mut current = ctx.body_parents.get(&body_id).copied();
  while let Some(parent) = current {
    if !visited.insert(parent) {
      break;
    }
    let parent_result = check_body(db, parent);
    let Some(meta) = ctx.body_info.get(&parent).copied() else {
      current = ctx.body_parents.get(&parent).copied();
      continue;
    };
    let Some(hir_id) = meta.hir else {
      current = ctx.body_parents.get(&parent).copied();
      continue;
    };
    let Some(lowered) = db
      .file_input(meta.file)
      .and_then(|input| lower_hir_for(db, input).lowered)
    else {
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
    let enclosing = matches!(meta.kind, HirBodyKind::TopLevel)
      .then_some(child_span)
      .flatten();
    seed_type_decls_from_body(
      ctx,
      &lowered,
      body,
      binding_defs,
      &mut seen_names,
      enclosing,
    );
    current = ctx.body_parents.get(&parent).copied();
  }
}

fn seed_enclosing_named_exprs(
  db: &dyn Db,
  ctx: &BodyCheckContext,
  body_id: BodyId,
  bindings: &mut HashMap<String, TypeId>,
  binding_defs: &mut HashMap<String, DefId>,
  seen_names: &mut HashSet<String>,
  unknown: TypeId,
) {
  let mut child = body_id;
  let mut current = ctx.body_parents.get(&body_id).copied();
  let mut visited = HashSet::new();
  while let Some(parent) = current {
    if !visited.insert(parent) {
      break;
    }
    let Some(meta) = ctx.body_info.get(&parent).copied() else {
      current = ctx.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    let Some(hir_id) = meta.hir else {
      current = ctx.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    let Some(lowered) = db
      .file_input(meta.file)
      .and_then(|input| lower_hir_for(db, input).lowered)
    else {
      current = ctx.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    let Some(parent_body) = lowered.body(hir_id) else {
      current = ctx.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    for expr in parent_body.exprs.iter() {
      match &expr.kind {
        hir_js::ExprKind::ClassExpr { def, body, name } => {
          if *body != child {
            continue;
          }
          let Some(name_id) = *name else {
            continue;
          };
          let Some(name) = lowered.names.resolve(name_id) else {
            continue;
          };
          if name.is_empty() || name.starts_with('<') {
            continue;
          }
          if !seen_names.insert(name.to_string()) {
            continue;
          }
          binding_defs.insert(name.to_string(), *def);
          if let Some(ty) = class_expr_ctor_ty_from_ctx(ctx, *def, expr.span) {
            bindings.insert(name.to_string(), ty);
          }
        }
        hir_js::ExprKind::FunctionExpr {
          def,
          body,
          name,
          is_arrow: false,
        } => {
          if *body != child {
            continue;
          }
          let Some(name_id) = *name else {
            continue;
          };
          let Some(name) = lowered.names.resolve(name_id) else {
            continue;
          };
          if name.is_empty() || name.starts_with('<') {
            continue;
          }
          if !seen_names.insert(name.to_string()) {
            continue;
          }
          binding_defs.insert(name.to_string(), *def);
          let ty = ctx.interned_def_types.get(def).copied().unwrap_or(unknown);
          if !matches!(ctx.store.type_kind(ty), TypeKind::Unknown) {
            bindings.insert(name.to_string(), ty);
          }
        }
        _ => {}
      }
    }
    current = ctx.body_parents.get(&parent).copied();
    child = parent;
  }
}

fn class_expr_ctor_ty_from_ctx(
  ctx: &BodyCheckContext,
  type_def: DefId,
  expr_span: TextRange,
) -> Option<TypeId> {
  // Prefer same-span constructable interned types (value-side synthetic defs
  // share the class-expression span with the type-side def).
  for (other_def, other_span) in ctx.def_id_spans.iter() {
    if *other_span != expr_span {
      continue;
    }
    if let Some(ty) = ctx.interned_def_types.get(other_def).copied() {
      if crate::check::hir_body::type_has_construct_signature(ctx.store.as_ref(), ty) {
        return Some(ctx.store.canon(ty));
      }
    }
  }
  // Fallback: type-side interned type when it already carries construct sigs.
  if let Some(ty) = ctx.interned_def_types.get(&type_def).copied() {
    if crate::check::hir_body::type_has_construct_signature(ctx.store.as_ref(), ty) {
      return Some(ctx.store.canon(ty));
    }
  }
  None
}

fn seed_type_decls_from_body(
  ctx: &BodyCheckContext,
  lowered: &hir_js::LowerResult,
  body: &HirBody,
  binding_defs: &mut HashMap<String, DefId>,
  seen_names: &mut HashSet<String>,
  enclosing: Option<TextRange>,
) {
  for stmt_id in body.root_stmts.iter().copied() {
    seed_type_decls_from_stmt(
      ctx,
      lowered,
      body,
      stmt_id,
      binding_defs,
      seen_names,
      enclosing,
      /*in_enclosing_block*/ false,
    );
  }
}

fn span_encloses(outer: TextRange, inner: TextRange) -> bool {
  outer.start <= inner.start && outer.end >= inner.end
}

fn seed_type_decls_from_stmt(
  ctx: &BodyCheckContext,
  lowered: &hir_js::LowerResult,
  body: &HirBody,
  stmt_id: hir_js::StmtId,
  binding_defs: &mut HashMap<String, DefId>,
  seen_names: &mut HashSet<String>,
  enclosing: Option<TextRange>,
  in_enclosing_block: bool,
) {
  let Some(stmt) = body.stmts.get(stmt_id.0 as usize) else {
    return;
  };
  match &stmt.kind {
    hir_js::StmtKind::Decl(def_id) => {
      // File-root decls are already in `file_bindings`. When filtering by an
      // enclosing body span, only nested (namespace/block) decls may seed —
      // and they overwrite so `namespace { class A }` shadows outer `class A`.
      if enclosing.is_some() && !in_enclosing_block {
        return;
      }
      let Some(kind) = ctx.def_kinds.get(def_id) else {
        return;
      };
      if !matches!(
        kind,
        crate::DefKind::Class(_)
          | crate::DefKind::Enum(_)
          | crate::DefKind::Interface(_)
          | crate::DefKind::TypeAlias(_)
      ) {
        return;
      }
      let Some(hir_def) = lowered.def(*def_id) else {
        return;
      };
      let Some(name) = lowered.names.resolve(hir_def.name) else {
        return;
      };
      if name.is_empty() || name.starts_with('<') {
        return;
      }
      if in_enclosing_block {
        seen_names.insert(name.to_string());
        binding_defs.insert(name.to_string(), *def_id);
        return;
      }
      if !seen_names.insert(name.to_string()) {
        return;
      }
      binding_defs.insert(name.to_string(), *def_id);
    }
    hir_js::StmtKind::Block(stmts) => {
      let child_in_block = match enclosing {
        Some(enc) if span_encloses(stmt.span, enc) => true,
        Some(_) => return,
        None => in_enclosing_block,
      };
      for child in stmts.iter().copied() {
        seed_type_decls_from_stmt(
          ctx,
          lowered,
          body,
          child,
          binding_defs,
          seen_names,
          enclosing,
          child_in_block,
        );
      }
    }
    hir_js::StmtKind::If {
      consequent,
      alternate,
      ..
    } => {
      seed_type_decls_from_stmt(
        ctx,
        lowered,
        body,
        *consequent,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
      if let Some(alt) = *alternate {
        seed_type_decls_from_stmt(
          ctx,
          lowered,
          body,
          alt,
          binding_defs,
          seen_names,
          enclosing,
          in_enclosing_block,
        );
      }
    }
    hir_js::StmtKind::While { body: inner, .. }
    | hir_js::StmtKind::DoWhile { body: inner, .. }
    | hir_js::StmtKind::For { body: inner, .. }
    | hir_js::StmtKind::ForIn { body: inner, .. }
    | hir_js::StmtKind::Labeled { body: inner, .. }
    | hir_js::StmtKind::With { body: inner, .. } => {
      seed_type_decls_from_stmt(
        ctx,
        lowered,
        body,
        *inner,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
    }
    hir_js::StmtKind::Switch { cases, .. } => {
      for case in cases.iter() {
        for child in case.consequent.iter().copied() {
          seed_type_decls_from_stmt(
            ctx,
            lowered,
            body,
            child,
            binding_defs,
            seen_names,
            enclosing,
            in_enclosing_block,
          );
        }
      }
    }
    hir_js::StmtKind::Try {
      block,
      catch,
      finally_block,
    } => {
      seed_type_decls_from_stmt(
        ctx,
        lowered,
        body,
        *block,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
      if let Some(catch) = catch {
        seed_type_decls_from_stmt(
          ctx,
          lowered,
          body,
          catch.body,
          binding_defs,
          seen_names,
          enclosing,
          in_enclosing_block,
        );
      }
      if let Some(finally) = finally_block {
        seed_type_decls_from_stmt(
          ctx,
          lowered,
          body,
          *finally,
          binding_defs,
          seen_names,
          enclosing,
          in_enclosing_block,
        );
      }
    }
    _ => {}
  }
}

fn function_expr_span(db: &dyn Db, ctx: &BodyCheckContext, body_id: BodyId) -> Option<TextRange> {
  let mut visited = HashSet::new();
  let mut current = ctx.body_parents.get(&body_id).copied();
  while let Some(parent) = current {
    if !visited.insert(parent) {
      break;
    }
    let Some(meta) = ctx.body_info.get(&parent).copied() else {
      current = ctx.body_parents.get(&parent).copied();
      continue;
    };
    let Some(hir_body_id) = meta.hir else {
      current = ctx.body_parents.get(&parent).copied();
      continue;
    };
    let Some(lowered) = db
      .file_input(meta.file)
      .and_then(|input| lower_hir_for(db, input).lowered)
    else {
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

/// Build a DA alias map for `file`, including imported type aliases resolved
/// through the export graph (re-export chains included).
fn da_type_alias_map_for_file<'a>(
  db: &dyn Db,
  ctx: &BodyCheckContext,
  file: FileId,
  lowered: &'a hir_js::LowerResult,
  pinned: &'a mut Vec<Arc<hir_js::LowerResult>>,
) -> DaTypeAliasMap<'a> {
  // Pass 1: collect import → (alias body via def span) or nullary type_id.
  enum ImportDaLink {
    Body {
      local: hir_js::NameId,
      alias_file: FileId,
      alias_span: TextRange,
    },
    Nullary {
      local: hir_js::NameId,
      ty: InternedTypeId,
    },
  }
  let mut import_links: Vec<ImportDaLink> = Vec::new();
  for import in lowered.hir.imports.iter() {
    let hir_js::ImportKind::Es(es) = &import.kind else {
      continue;
    };
    for named in es.named.iter() {
      let Some(local_str) = lowered.names.resolve(named.local) else {
        continue;
      };
      let Some(binding) = ctx
        .file_bindings
        .get(&file)
        .and_then(|bindings| bindings.get(local_str))
      else {
        continue;
      };
      let Some(import_def) = binding.def else {
        continue;
      };
      match resolve_imported_type_alias_link(ctx, import_def) {
        Some(ImportedAliasLink::Def(alias_def)) => {
          let Some(alias_file) = ctx.def_files.get(&alias_def).copied() else {
            continue;
          };
          let Some(alias_span) = ctx.def_id_spans.get(&alias_def).copied() else {
            continue;
          };
          if pinned.iter().all(|l| l.hir.file != alias_file) {
            if let Some(foreign) = db
              .file_input(alias_file)
              .and_then(|input| lower_hir_for(db, input).lowered)
            {
              pinned.push(foreign);
            }
          }
          import_links.push(ImportDaLink::Body {
            local: named.local,
            alias_file,
            alias_span,
          });
        }
        Some(ImportedAliasLink::TypeId(ty)) => {
          import_links.push(ImportDaLink::Nullary {
            local: named.local,
            ty,
          });
        }
        None => {}
      }
    }
  }

  // Pass 2: borrow pinned lowereds / record nullary facts into the map.
  let mut map = DaTypeAliasMap::from_lowered(lowered);
  for link in import_links {
    match link {
      ImportDaLink::Body {
        local,
        alias_file,
        alias_span,
      } => {
        let Some(foreign) = pinned.iter().find(|l| l.hir.file == alias_file) else {
          continue;
        };
        map.register_file_aliases(foreign);
        let Some(hir_def) = foreign
          .defs
          .iter()
          .find(|d| d.path.kind == hir_js::DefKind::TypeAlias && d.span == alias_span)
        else {
          continue;
        };
        let Some(export_name) = foreign.names.resolve(hir_def.name) else {
          continue;
        };
        let Some(body) = map
          .by_qualified
          .get(&(alias_file.0, export_name.to_string()))
          .copied()
        else {
          continue;
        };
        map.link_alias_body(local, body);
      }
      ImportDaLink::Nullary { local, ty } => {
        map.link_nullary_exempt(local, type_id_is_da_exempt(&ctx.store, ty));
      }
    }
  }
  map
}

enum ImportedAliasLink {
  Def(DefId),
  TypeId(InternedTypeId),
}

/// Follow `Import` / re-export edges to a `TypeAlias` def, or a resolved
/// export `type_id` when the re-export has no local def (common for
/// `export type { A as B } from "./mod"`).
fn resolve_imported_type_alias_link(
  ctx: &BodyCheckContext,
  start: DefId,
) -> Option<ImportedAliasLink> {
  let mut current = start;
  for _ in 0..8 {
    let kind = ctx.def_kinds.get(&current)?;
    match kind {
      crate::DefKind::TypeAlias(_) => return Some(ImportedAliasLink::Def(current)),
      crate::DefKind::Import(imp) => {
        let crate::ImportTarget::File(target_file) = &imp.target else {
          return None;
        };
        let exports = ctx.exports.get(target_file)?;
        let entry = exports.get(&imp.original)?;
        if let Some(def) = entry.def {
          current = def;
          continue;
        }
        if let Some(ty) = entry.type_id {
          return Some(ImportedAliasLink::TypeId(ty));
        }
        return None;
      }
      _ => return None,
    }
  }
  None
}

fn contextual_callable_for_body(
  db: &dyn Db,
  ctx: &BodyCheckContext,
  body_id: BodyId,
  func_span: TextRange,
) -> Option<TypeId> {
  let store = &ctx.store;
  let mut visited = HashSet::new();
  let mut current = ctx.body_parents.get(&body_id).copied();
  while let Some(parent) = current {
    if !visited.insert(parent) {
      break;
    }
    let parent_result = check_body(db, parent);
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
    current = ctx.body_parents.get(&parent).copied();
  }
  None
}
