use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use salsa::Setter;

use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  lower_file_with_diagnostics, ExportDefaultValue, ExportKind, ExprKind, FileKind as HirFileKind,
  LowerResult, ObjectProperty, StmtKind,
};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::ts as sem_ts;
use types_ts_interned::{PrimitiveIds, TypeStore};

use crate::codes;
use crate::db::inputs::{
  CancellationToken, CancelledInput, CompilerOptionsInput, FileInput, ModuleResolutionInput,
  RootsInput,
};
use crate::db::spans::{expr_at_from_spans, FileSpanIndex};
use crate::db::symbols::{LocalSymbolInfo, SymbolIndex};
use crate::db::{symbols, Db, ModuleKey};
use crate::lib_support::{CompilerOptions, FileKind};
use crate::parse_metrics;
use crate::profile::QueryKind;
use crate::queries::parse as parser;
use crate::sem_hir::sem_hir_from_lower;
use crate::semantic_js::SymbolId;
use crate::symbols::SymbolBinding;
use crate::FileKey;
use crate::SymbolOccurrence;
use crate::{BodyId, DefId, ExprId, TypeId};

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

pub mod body_check {
  use std::cell::RefCell;
  use std::collections::{HashMap, HashSet};
  use std::fmt;
  use std::sync::atomic::{AtomicUsize, Ordering};
  use std::sync::{Arc, OnceLock, RwLock};
  use std::time::Instant;

  use diagnostics::{FileId, Span, TextRange};
  use hir_js::{
    Body as HirBody, BodyId as HirBodyId, BodyKind as HirBodyKind, DefId as HirDefId, NameInterner,
  };
  use hir_js::{PatId as HirPatId, PatKind as HirPatKind};
  use parse_js::ast::node::Node;
  use parse_js::ast::stx::TopLevel;
  use types_ts_interned::{RelateCtx, TypeId as InternedTypeId, TypeParamId, TypeStore};

  use crate::check::caches::CheckerCaches;
  use crate::check::hir_body::{
    check_body_with_env, check_body_with_expander, BindingTypeResolver,
  };
  use crate::codes;
  use crate::db::expander::{DbTypeExpander, TypeExpanderDb};
  use crate::lib_support::{CacheMode, CacheOptions};
  use crate::profile::{QueryKind, QueryStatsCollector};
  use crate::program::check::relate_hooks;
  use crate::{BodyCheckResult, BodyId, DefId, PatId, SymbolBinding, TypeId};

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
    pub interned_def_types: HashMap<DefId, InternedTypeId>,
    pub interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
    pub asts: HashMap<FileId, Arc<Node<TopLevel>>>,
    pub lowered: HashMap<FileId, Arc<hir_js::LowerResult>>,
    pub body_info: HashMap<BodyId, BodyInfo>,
    pub body_parents: HashMap<BodyId, BodyId>,
    pub global_bindings: HashMap<String, SymbolBinding>,
    pub file_bindings: HashMap<FileId, HashMap<String, SymbolBinding>>,
    pub def_spans: HashMap<(FileId, TextRange), DefId>,
    pub checker_caches: CheckerCaches,
    pub cache_mode: CacheMode,
    pub cache_options: CacheOptions,
    pub query_stats: QueryStatsCollector,
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

    fn guard(self: Arc<Self>) -> ParallelGuard {
      let current = self.active.fetch_add(1, Ordering::SeqCst) + 1;
      self.max_active.fetch_max(current, Ordering::SeqCst);
      ParallelGuard { tracker: self }
    }
  }

  pub struct ParallelGuard {
    tracker: Arc<ParallelTracker>,
  }

  impl Drop for ParallelGuard {
    fn drop(&mut self) {
      self.tracker.active.fetch_sub(1, Ordering::SeqCst);
    }
  }

  static PARALLEL_TRACKER: OnceLock<RwLock<Option<Arc<ParallelTracker>>>> = OnceLock::new();

  fn tracker_slot() -> &'static RwLock<Option<Arc<ParallelTracker>>> {
    PARALLEL_TRACKER.get_or_init(|| RwLock::new(None))
  }

  pub fn set_parallel_tracker(tracker: Option<Arc<ParallelTracker>>) {
    *tracker_slot().write().unwrap() = tracker;
  }

  pub fn parallel_guard() -> Option<ParallelGuard> {
    tracker_slot()
      .read()
      .unwrap()
      .as_ref()
      .cloned()
      .map(|tracker| tracker.guard())
  }

  impl BodyCheckDb {
    pub fn new(context: BodyCheckContext) -> Self {
      Self {
        context: Arc::new(context),
        memo: RefCell::new(HashMap::new()),
      }
    }
  }

  impl TypeExpanderDb for BodyCheckContext {
    fn type_store(&self) -> Arc<TypeStore> {
      Arc::clone(&self.store)
    }

    fn decl_type(&self, def: DefId) -> Option<InternedTypeId> {
      self.interned_def_types.get(&def).copied()
    }

    fn type_params(&self, def: DefId) -> Arc<[TypeParamId]> {
      self
        .interned_type_params
        .get(&def)
        .cloned()
        .map(Arc::from)
        .unwrap_or_else(|| Arc::from([]))
    }

    fn type_of_def(&self, def: DefId) -> Option<InternedTypeId> {
      self.interned_def_types.get(&def).copied()
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

    fn compute_body(&self, body_id: BodyId) -> Arc<BodyCheckResult> {
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
          kind: HirBodyKind::TopLevel,
          exprs: Vec::new(),
          stmts: Vec::new(),
          pats: Vec::new(),
          root_stmts: Vec::new(),
          function: None,
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
      let mut result = check_body_with_expander(
        body_id,
        body,
        &lowered.names,
        meta.file,
        &*ast,
        Arc::clone(&ctx.store),
        &caches,
        &bindings,
        (!binding_defs.is_empty())
          .then(|| Arc::new(BindingTypeResolver::new(binding_defs)) as Arc<_>),
        Some(&expander),
        None,
      );

      if !body.exprs.is_empty() && matches!(meta.kind, HirBodyKind::Function) {
        let mut initial_env: HashMap<_, _> = HashMap::new();
        if let Some(function) = body.function.as_ref() {
          for param in function.params.iter() {
            if let Some(ty) = result.pat_types.get(param.pat.0 as usize).copied() {
              if ty != prim.unknown {
                if let Some(pat) = body.pats.get(param.pat.0 as usize) {
                  if let HirPatKind::Ident(name) = pat.kind {
                    initial_env.insert(name, ty);
                  }
                }
              }
            }
          }
        }
        for expr in body.exprs.iter() {
          if let hir_js::ExprKind::Ident(name_id) = expr.kind {
            if initial_env.contains_key(&name_id) {
              continue;
            }
            if let Some(name) = lowered.names.resolve(name_id) {
              if let Some(ty) = bindings.get(name) {
                initial_env.insert(name_id, *ty);
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
              if existing == prim.unknown || narrower {
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
              if existing == prim.unknown || narrower {
                result.pat_types[idx] = *ty;
              }
            }
          }
        }
        if result.return_types.is_empty() && !flow_result.return_types.is_empty() {
          result.return_types = flow_result.return_types;
        }
        if result.diagnostics.is_empty() && !flow_result.diagnostics.is_empty() {
          result.diagnostics = flow_result.diagnostics;
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
  ) {
    let prim = ctx.store.primitive_ids();
    let Some(pat) = body.pats.get(pat_id.0 as usize) else {
      return;
    };
    let ty = result.pat_type(PatId(pat_id.0)).unwrap_or(prim.unknown);
    match &pat.kind {
      HirPatKind::Ident(name_id) => {
        if let Some(name) = names.resolve(*name_id) {
          if ty != prim.unknown {
            bindings.entry(name.to_string()).or_insert(ty);
          }
          if let Some(def_id) = ctx.def_spans.get(&(file, pat.span)).copied() {
            binding_defs.entry(name.to_string()).or_insert(def_id);
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
          );
        }
        if let Some(rest) = arr.rest {
          record_pat(ctx, rest, body, names, result, bindings, binding_defs, file);
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
          );
        }
        if let Some(rest) = obj.rest {
          record_pat(ctx, rest, body, names, result, bindings, binding_defs, file);
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
      let ty = binding.def.map(|d| map_def_ty(d)).unwrap_or(unknown);
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
        );
      }
      current = ctx.body_parents.get(&parent).copied();
    }
    let _ = unknown;
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
  let _timer = db
    .profiler()
    .map(|profiler| profiler.timer(QueryKind::Parse, false));
  parse_metrics::record_parse_call();
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

#[salsa::tracked]
fn symbol_index_for(db: &dyn Db, file: FileInput) -> SymbolIndex {
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
  let ast = match parse_with_options(
    &source,
    ParseOptions {
      dialect,
      source_type: SourceType::Module,
    },
  ) {
    Ok(ast) => ast,
    Err(_) => return SymbolIndex::empty(),
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

#[salsa::tracked(recovery_fn = check_body_cycle)]
pub fn check_body(db: &dyn TypeDb, def: DefId, _seed: ()) -> TypeId {
  // The unit seed mirrors `decl_types_in_file` to avoid introducing synthetic
  // salsa structs for every definition key.
  let store = type_store(db).arc();
  let fallback = store.primitive_ids().unknown;
  let Some(decl) = decl_types_for_def(db, def) else {
    return fallback;
  };
  let Some(init) = decl.initializer.clone() else {
    return fallback;
  };
  eval_initializer(db, &store, init)
}

fn check_body_cycle(db: &dyn TypeDb, _cycle: &salsa::Cycle, _def: DefId, _seed: ()) -> TypeId {
  // Bodies are part of the same cycle when an initializer references its own
  // definition. Recover with `any` to mirror `type_of_def`'s fallback and avoid
  // panicking on self-references.
  type_store(db).arc().primitive_ids().any
}

#[salsa::tracked(recovery_fn = type_of_def_cycle)]
pub fn type_of_def(db: &dyn TypeDb, def: DefId, _seed: ()) -> TypeId {
  // The extra seed enables the tracked query to memoize arbitrary `DefId`s
  // without forcing them to implement salsa's struct traits.
  // Track compiler options changes even if we do not branch on them yet.
  let _options = type_compiler_options(db);
  let store = type_store(db).arc();
  let fallback = store.primitive_ids().any;

  let base = base_type(db, &store, def, fallback);

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
          base_type(db, &store, *member, fallback)
        };
        members.push(ty);
      }
      return store.union(members);
    }
  }

  base
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
}

impl Default for TypesDatabase {
  fn default() -> Self {
    Self {
      storage: salsa::Storage::default(),
      compiler_options: None,
      type_store: None,
      files: None,
      decls: BTreeMap::new(),
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
}

impl TypesDatabase {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn snapshot(&self) -> Self {
    self.clone()
  }

  pub fn set_compiler_options(&mut self, options: CompilerOptions) {
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

/// Derived query that aggregates diagnostics from parsing, lowering, binding,
/// and any additional sources (e.g. body checking) across all reachable files.
pub fn program_diagnostics(
  db: &dyn Db,
  additional: impl IntoIterator<Item = Diagnostic>,
) -> Arc<[Diagnostic]> {
  let files = all_files(db);
  let mut parse_diags = Vec::new();
  let mut lower_diags = Vec::new();
  for file in files.iter() {
    let parsed = parse(db, *file);
    parse_diags.extend(parsed.diagnostics.into_iter());
    let lowered = lower_hir(db, *file);
    lower_diags.extend(lowered.diagnostics.into_iter());
  }
  let semantics = ts_semantics(db);
  aggregate_program_diagnostics(
    parse_diags,
    lower_diags,
    semantics.diagnostics.iter().cloned(),
    additional,
  )
}
