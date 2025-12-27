pub mod analysis;
pub mod cfg;
pub mod decompile;
pub mod dom;
pub mod eval;
pub mod graph;
pub mod il;
pub mod opt;
pub mod ssa;
pub mod symbol;
pub mod util;

pub use crate::decompile::program_to_js;
pub use crate::decompile::{program_to_ast, DecompileOptions};
use crate::il::inst::Inst;
use crate::util::counter::Counter;
use ahash::HashMap;
use ahash::HashSet;
use analysis::defs::calculate_defs;
use cfg::bblock::convert_insts_to_bblocks;
use cfg::cfg::Cfg;
use dashmap::DashMap;
use dom::Dom;
use hir_js::lower_file;
use hir_js::Body;
use hir_js::BodyId;
use hir_js::ExprId;
use hir_js::FileKind as HirFileKind;
use hir_js::LowerResult;
use hir_js::NameId;
use hir_js::NameInterner;
use hir_js::PatId;
use opt::optpass_cfg_prune::optpass_cfg_prune;
use opt::optpass_dvn::optpass_dvn;
use opt::optpass_impossible_branches::optpass_impossible_branches;
use opt::optpass_redundant_assigns::optpass_redundant_assigns;
use opt::optpass_trivial_dce::optpass_trivial_dce;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::parse;
use semantic_js::js::ScopeKind;
pub use semantic_js::js::TopLevelMode;
use serde::Serialize;
use ssa::ssa_deconstruct::deconstruct_ssa;
use ssa::ssa_insert_phis::insert_phis_for_ssa_construction;
use ssa::ssa_rename::rename_targets_for_ssa_construction;
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use symbol::semantics::{
  assoc_declared_symbol, assoc_resolved_symbol, JsSymbols, ScopeId, SymbolId,
};
use symbol::var_analysis::VarAnalysis;
use util::debug::OptimizerDebug;

pub use diagnostics::{Diagnostic, FileId, Span, TextRange};

const SOURCE_FILE: FileId = FileId(0);

pub type OptimizeResult<T> = Result<T, Vec<Diagnostic>>;

fn diagnostic_with_span(code: &'static str, message: impl Into<String>, loc: Loc) -> Diagnostic {
  let (range, note) = loc.to_diagnostics_range_with_note();
  let mut diagnostic = Diagnostic::error(code, message, Span::new(SOURCE_FILE, range));
  if let Some(note) = note {
    diagnostic = diagnostic.with_note(note);
  }
  diagnostic
}

fn unsupported_syntax(loc: Loc, message: impl Into<String>) -> Vec<Diagnostic> {
  vec![diagnostic_with_span("OPT0002", message, loc)]
}

fn diagnostic_with_range(
  code: &'static str,
  message: impl Into<String>,
  range: TextRange,
) -> Diagnostic {
  Diagnostic::error(code, message, Span::new(SOURCE_FILE, range))
}

fn unsupported_syntax_range(range: TextRange, message: impl Into<String>) -> Vec<Diagnostic> {
  vec![diagnostic_with_range("OPT0002", message, range)]
}

fn use_before_declaration(name: &str, loc: Loc) -> Diagnostic {
  diagnostic_with_span(
    "OPT0001",
    format!("use of `{name}` before declaration"),
    loc,
  )
}

fn sort_diagnostics(diagnostics: &mut [Diagnostic]) {
  diagnostics.sort_by(|a, b| {
    a.primary
      .file
      .cmp(&b.primary.file)
      .then(a.primary.range.start.cmp(&b.primary.range.start))
      .then(a.primary.range.end.cmp(&b.primary.range.end))
      .then(a.code.cmp(&b.code))
      .then(a.message.cmp(&b.message))
  });
}

// The top level is considered a function (the optimizer concept, not parser or symbolizer).
#[derive(Debug, Serialize)]
pub struct ProgramFunction {
  pub debug: Option<OptimizerDebug>,
  pub body: Cfg,
}

#[derive(Debug, Serialize)]
pub struct ProgramSymbol {
  pub id: SymbolId,
  pub name: String,
  pub scope: ScopeId,
  pub captured: bool,
}

#[derive(Debug, Serialize)]
pub struct ProgramFreeSymbols {
  pub top_level: Vec<SymbolId>,
  pub functions: Vec<Vec<SymbolId>>, // Index aligned with Program::functions.
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ProgramScopeKind {
  Global,
  Module,
  Class,
  NonArrowFunction,
  ArrowFunction,
  Block,
  FunctionExpressionName,
}

impl From<ScopeKind> for ProgramScopeKind {
  fn from(kind: ScopeKind) -> Self {
    match kind {
      ScopeKind::Global => ProgramScopeKind::Global,
      ScopeKind::Module => ProgramScopeKind::Module,
      ScopeKind::Class => ProgramScopeKind::Class,
      ScopeKind::NonArrowFunction => ProgramScopeKind::NonArrowFunction,
      ScopeKind::ArrowFunction => ProgramScopeKind::ArrowFunction,
      ScopeKind::Block => ProgramScopeKind::Block,
      ScopeKind::FunctionExpressionName => ProgramScopeKind::FunctionExpressionName,
    }
  }
}

#[derive(Debug, Serialize)]
pub struct ProgramScope {
  pub id: ScopeId,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub parent: Option<ScopeId>,
  pub kind: ProgramScopeKind,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub symbols: Vec<SymbolId>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub children: Vec<ScopeId>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub tdz_bindings: Vec<SymbolId>,
  pub is_dynamic: bool,
  pub has_direct_eval: bool,
}

#[derive(Debug, Serialize)]
pub struct ProgramSymbols {
  pub symbols: Vec<ProgramSymbol>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub free_symbols: Option<ProgramFreeSymbols>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub names: Vec<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub scopes: Vec<ProgramScope>,
}

#[derive(Clone, Default, Debug)]
pub(crate) struct HirSymbolBindings {
  exprs: HashMap<BodyId, HashMap<ExprId, Option<SymbolId>>>,
  pats: HashMap<BodyId, HashMap<PatId, Option<SymbolId>>>,
}

impl HirSymbolBindings {
  fn symbol_for_expr(&self, body: BodyId, expr: ExprId) -> Option<SymbolId> {
    self
      .exprs
      .get(&body)
      .and_then(|m| m.get(&expr))
      .and_then(|s| *s)
  }

  fn symbol_for_pat(&self, body: BodyId, pat: PatId) -> Option<SymbolId> {
    self
      .pats
      .get(&body)
      .and_then(|m| m.get(&pat))
      .and_then(|s| *s)
  }
}

fn collect_hir_symbol_bindings(ast: &mut Node<TopLevel>, lower: &LowerResult) -> HirSymbolBindings {
  use derive_visitor::{DriveMut, VisitorMut};
  use parse_js::ast::expr::pat::IdPat;
  use parse_js::ast::expr::IdExpr;

  #[derive(VisitorMut)]
  #[visitor(IdExprNode(enter), IdPatNode(enter))]
  struct Collector<'a> {
    span_map: &'a hir_js::span_map::SpanMap,
    expr_spans: BTreeMap<TextRange, Option<SymbolId>>,
    pat_spans: BTreeMap<TextRange, Option<SymbolId>>,
  }

  type IdExprNode = Node<IdExpr>;
  type IdPatNode = Node<IdPat>;

  impl<'a> Collector<'a> {
    fn map_symbol(&self, assoc: &NodeAssocData) -> Option<SymbolId> {
      assoc_declared_symbol(assoc).or_else(|| assoc_resolved_symbol(assoc))
    }

    fn offsets(span: TextRange) -> impl Iterator<Item = u32> {
      let mut offsets = vec![span.start];
      if span.end > span.start {
        let mid = span.start + (span.end - span.start) / 2;
        let end = span.end.saturating_sub(1);
        offsets.push(mid);
        offsets.push(end);
      }
      offsets.sort_unstable();
      offsets.dedup();
      offsets.into_iter()
    }

    fn expr_for_span(&self, span: TextRange) -> Option<(BodyId, ExprId)> {
      for offset in Self::offsets(span) {
        if let Some(span) = self.span_map.expr_span_at_offset(offset) {
          return Some(span.id);
        }
      }
      None
    }

    fn pat_for_span(&self, span: TextRange) -> Option<(BodyId, PatId)> {
      for offset in Self::offsets(span) {
        if let Some(span) = self.span_map.pat_span_at_offset(offset) {
          return Some(span.id);
        }
      }
      None
    }

    fn record_expr(&mut self, span: TextRange, sym: Option<SymbolId>) {
      self.expr_spans.insert(span, sym);
      self.pat_spans.insert(span, sym);
    }

    fn record_pat(&mut self, span: TextRange, sym: Option<SymbolId>) {
      self.pat_spans.insert(span, sym);
    }

    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      let span = TextRange::new(node.loc.start_u32(), node.loc.end_u32());
      let sym = self.map_symbol(&node.assoc);
      self.record_expr(span, sym);
    }

    fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
      let span = TextRange::new(node.loc.start_u32(), node.loc.end_u32());
      let sym = self.map_symbol(&node.assoc);
      self.record_pat(span, sym);
    }
  }

  let span_map = &lower.hir.span_map;
  let mut bindings = HirSymbolBindings::default();
  let mut collector = Collector {
    span_map,
    expr_spans: BTreeMap::new(),
    pat_spans: BTreeMap::new(),
  };
  ast.drive_mut(&mut collector);

  for (span, sym) in collector.expr_spans.iter() {
    if let Some((body, expr_id)) = collector.expr_for_span(*span) {
      bindings
        .exprs
        .entry(body)
        .or_default()
        .insert(expr_id, *sym);
    }
  }
  for (span, sym) in collector.pat_spans.iter() {
    if let Some((body, pat_id)) = collector.pat_for_span(*span) {
      bindings.pats.entry(body).or_default().insert(pat_id, *sym);
    }
  }

  for (body_id, idx) in &lower.body_index {
    let body = &lower.bodies[*idx];
    let exprs = bindings.exprs.entry(*body_id).or_default();
    for (idx, expr) in body.exprs.iter().enumerate() {
      let id = ExprId(idx as u32);
      exprs.entry(id).or_insert_with(|| {
        collector
          .expr_spans
          .get(&expr.span)
          .copied()
          .unwrap_or(None)
      });
    }
    let pats = bindings.pats.entry(*body_id).or_default();
    for (idx, pat) in body.pats.iter().enumerate() {
      let id = PatId(idx as u32);
      pats
        .entry(id)
        .or_insert_with(|| collector.pat_spans.get(&pat.span).copied().unwrap_or(None));
    }
  }

  bindings
}

pub(crate) fn build_program_function(
  program: &ProgramCompiler,
  insts: Vec<Inst>,
  mut c_label: Counter,
  mut c_temp: Counter,
) -> ProgramFunction {
  let mut dbg = program.debug.then(|| OptimizerDebug::new());
  let mut dbg_checkpoint = |name: &str, cfg: &Cfg| {
    dbg.as_mut().map(|dbg| dbg.add_step(name, cfg));
  };

  let (bblocks, bblock_order) = convert_insts_to_bblocks(insts, &mut c_label);
  let mut cfg = Cfg::from_bblocks(bblocks, bblock_order);
  // Prune unreachable blocks from 0. This is necessary for dominance calculation to be correct (basic example: every block should be dominated by 0, but if there's an unreachable block it'll make all its descendants not dominated by 0).
  // This can happen due to user code (unreachable code) or by us, because we split after a `goto` which makes the new other-split-half block unreachable (this block is usually empty).
  cfg.find_and_pop_unreachable();

  let mut defs = calculate_defs(&cfg);
  dbg_checkpoint("source", &cfg);

  // Construct SSA.
  let dom = Dom::calculate(&cfg);
  insert_phis_for_ssa_construction(&mut defs, &mut cfg, &dom);
  dbg_checkpoint("ssa_insert_phis", &cfg);
  rename_targets_for_ssa_construction(&mut cfg, &dom, &mut c_temp);
  dbg_checkpoint("ssa_rename_targets", &cfg);

  // Optimisation passes:
  // - Dominator-based value numbering.
  // - Trivial dead code elimination.
  // Drop defs as it likely will be invalid after even one pass.
  drop(defs);
  for i in 1.. {
    let mut changed = false;

    // TODO Can we avoid recalculating these on every iteration i.e. mutate in-place when changing the CFG?
    let dom = Dom::calculate(&cfg);

    optpass_dvn(&mut changed, &mut cfg, &dom);
    dbg_checkpoint(&format!("opt{}_dvn", i), &cfg);
    optpass_trivial_dce(&mut changed, &mut cfg);
    dbg_checkpoint(&format!("opt{}_dce", i), &cfg);
    // TODO Isn't this really const/copy propagation to child Phi insts?
    optpass_redundant_assigns(&mut changed, &mut cfg);
    dbg_checkpoint(&format!("opt{}_redundant_assigns", i), &cfg);
    optpass_impossible_branches(&mut changed, &mut cfg);
    dbg_checkpoint(&format!("opt{}_impossible_branches", i), &cfg);
    optpass_cfg_prune(&mut changed, &mut cfg);
    dbg_checkpoint(&format!("opt{}_cfg_prune", i), &cfg);

    if !changed {
      break;
    }
  }

  // It's safe to calculate liveliness before removing Phi insts; after deconstructing, they always lie exactly between all parent bblocks and the head of the bblock, so their lifetimes are identical.
  deconstruct_ssa(&mut cfg, &mut c_label);
  dbg_checkpoint("ssa_deconstruct", &cfg);

  ProgramFunction {
    debug: dbg,
    body: cfg,
  }
}

pub(crate) fn compile_hir_body(
  program: &ProgramCompiler,
  body: BodyId,
) -> OptimizeResult<ProgramFunction> {
  let (insts, c_label, c_temp) = crate::il::s2i::stmt::translate_body(program, body)?;
  Ok(build_program_function(program, insts, c_label, c_temp))
}

#[cfg(feature = "legacy-ast-lowering")]
fn compile_js_ast_statements(
  program: &ProgramCompiler,
  statements: Vec<Node<Stmt>>,
) -> OptimizeResult<ProgramFunction> {
  let (insts, c_label, c_temp) =
    crate::il::s2i::legacy::translate_source_to_inst(program, statements)?;
  Ok(build_program_function(program, insts, c_label, c_temp))
}

pub type FnId = usize;

pub use decompile::structurer::{structure_cfg, BreakTarget, ControlTree, LoopLabel};

#[derive(Debug)]
pub struct ProgramCompilerInner {
  // Precomputed via VarAnalysis.
  pub foreign_vars: HashSet<SymbolId>,
  pub functions: DashMap<FnId, ProgramFunction>,
  pub next_fn_id: AtomicUsize,
  pub debug: bool,
  pub lower: Arc<LowerResult>,
  pub(crate) bindings: HirSymbolBindings,
  pub names: Arc<NameInterner>,
}

/// Our internal compiler state for a program.
/// We have a separate struct instead of using the public-facing Program.
/// It means we can use pub instead of pub(crate) fields and methods everywhere.
#[derive(Clone)]
pub struct ProgramCompiler(Arc<ProgramCompilerInner>);

impl Deref for ProgramCompiler {
  type Target = ProgramCompilerInner;

  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl ProgramCompiler {
  fn name_for(&self, name: NameId) -> String {
    self
      .names
      .resolve(name)
      .map(str::to_string)
      .unwrap_or_else(|| "<unknown>".to_string())
  }

  fn symbol_for_expr(&self, body: BodyId, expr: ExprId) -> Option<SymbolId> {
    self.bindings.symbol_for_expr(body, expr)
  }

  fn symbol_for_pat(&self, body: BodyId, pat: PatId) -> Option<SymbolId> {
    self.bindings.symbol_for_pat(body, pat)
  }

  fn body(&self, id: BodyId) -> &Body {
    self.lower.body(id).expect("body should exist")
  }
}

#[derive(Debug)]
pub struct Program {
  pub functions: Vec<ProgramFunction>,
  pub top_level: ProgramFunction,
  pub top_level_mode: TopLevelMode,
  pub symbols: Option<ProgramSymbols>,
}

/// Parse, symbolize, and compile source text in one step.
///
/// The provided source must be valid UTF-8; identifier handling and span math
/// operate on UTF-8 byte offsets. Validate and convert any raw byte buffers at
/// the I/O boundary before calling this helper.
pub fn compile_source(source: &str, mode: TopLevelMode, debug: bool) -> OptimizeResult<Program> {
  let top_level_node = parse(source).map_err(|err| vec![err.to_diagnostic(SOURCE_FILE)])?;
  Program::compile(top_level_node, mode, debug)
}

#[cfg(feature = "legacy-ast-lowering")]
pub fn compile_source_ast(
  source: &str,
  mode: TopLevelMode,
  debug: bool,
) -> OptimizeResult<Program> {
  let mut top_level_node = parse(source).map_err(|err| vec![err.to_diagnostic(SOURCE_FILE)])?;
  let lower = lower_file(SOURCE_FILE, HirFileKind::Ts, &top_level_node);
  let (semantics, _) = JsSymbols::bind(&mut top_level_node, mode, SOURCE_FILE);
  let VarAnalysis {
    foreign,
    use_before_decl,
    dynamic_scope,
    ..
  } = VarAnalysis::analyze(&mut top_level_node, &semantics);
  if let Some(loc) = dynamic_scope {
    return Err(unsupported_syntax(
      loc,
      "with statements introduce dynamic scope and are not supported",
    ));
  }
  if !use_before_decl.is_empty() {
    let mut diagnostics: Vec<_> = use_before_decl
      .into_iter()
      .map(|(_, (name, loc))| use_before_declaration(&name, loc))
      .collect();
    sort_diagnostics(&mut diagnostics);
    return Err(diagnostics);
  };
  let mut symbol_table = collect_symbol_table(&semantics, &foreign);
  let bindings = collect_hir_symbol_bindings(&mut top_level_node, &lower);
  let lower = Arc::new(lower);
  let program = ProgramCompiler(Arc::new(ProgramCompilerInner {
    foreign_vars: foreign.clone(),
    functions: DashMap::new(),
    next_fn_id: AtomicUsize::new(0),
    debug,
    lower: Arc::clone(&lower),
    bindings,
    names: Arc::clone(&lower.names),
  }));

  let TopLevel { body } = *top_level_node.stx;
  let top_level = crate::il::s2i::legacy::compile_js_statements(&program, body)?;
  let ProgramCompilerInner {
    functions,
    next_fn_id,
    ..
  } = Arc::try_unwrap(program.0).unwrap();
  let fn_count = next_fn_id.load(Ordering::Relaxed);
  let functions: Vec<_> = (0..fn_count)
    .map(|i| functions.remove(&i).unwrap().1)
    .collect();

  let free_symbols = ProgramFreeSymbols {
    top_level: collect_free_symbols(&top_level),
    functions: functions.iter().map(collect_free_symbols).collect(),
  };

  let has_any_symbols = !symbol_table.symbols.is_empty()
    || !free_symbols.top_level.is_empty()
    || free_symbols.functions.iter().any(|f| !f.is_empty());

  let symbols = if has_any_symbols {
    symbol_table.free_symbols = Some(free_symbols);
    Some(symbol_table)
  } else {
    None
  };

  Ok(Program {
    functions,
    top_level,
    top_level_mode: mode,
    symbols,
  })
}

fn collect_symbol_table(symbols: &JsSymbols, captured: &HashSet<SymbolId>) -> ProgramSymbols {
  fn collect_scope_symbols(
    symbols: &JsSymbols,
    scope: ScopeId,
    captured: &HashSet<SymbolId>,
    out: &mut Vec<ProgramSymbol>,
  ) {
    for (id, name) in symbols.symbols_in_scope(scope) {
      out.push(ProgramSymbol {
        id,
        name,
        scope,
        captured: captured.contains(&id),
      });
    }

    let mut children: Vec<_> = symbols.children(scope).collect();
    children.sort_by_key(|scope| scope.raw_id());
    for child in children {
      collect_scope_symbols(symbols, child, captured, out);
    }
  }

  let mut out_symbols = Vec::new();
  collect_scope_symbols(symbols, symbols.top_scope(), captured, &mut out_symbols);
  let mut scopes = Vec::with_capacity(symbols.semantics.scopes.len());
  for (scope_id, scope) in symbols.semantics.scopes.iter() {
    let id = ScopeId::from(*scope_id);
    let mut scope_symbols: Vec<_> = scope
      .iter_symbols_sorted()
      .map(|(_, symbol)| SymbolId::from(symbol))
      .collect();
    scope_symbols.sort_by_key(|sym| sym.raw_id());
    let mut children: Vec<_> = scope.children.iter().copied().map(Into::into).collect();
    children.sort_by_key(|child: &ScopeId| child.raw_id());
    let mut tdz_bindings: Vec<_> = scope.tdz_bindings.iter().copied().map(Into::into).collect();
    tdz_bindings.sort_by_key(|sym: &SymbolId| sym.raw_id());
    scopes.push(ProgramScope {
      id,
      parent: scope.parent.map(Into::into),
      kind: scope.kind.into(),
      symbols: scope_symbols,
      children,
      tdz_bindings,
      is_dynamic: scope.is_dynamic,
      has_direct_eval: scope.has_direct_eval,
    });
  }
  scopes.sort_by_key(|scope| scope.id.raw_id());
  ProgramSymbols {
    symbols: out_symbols,
    free_symbols: None,
    names: symbols
      .semantics
      .names
      .iter()
      .map(|(_, name)| name.clone())
      .collect(),
    scopes,
  }
}

fn collect_free_symbols(func: &ProgramFunction) -> Vec<SymbolId> {
  let mut free = HashSet::default();
  for (_, insts) in func.body.bblocks.all() {
    for inst in insts {
      match inst.t {
        il::inst::InstTyp::ForeignLoad | il::inst::InstTyp::ForeignStore => {
          free.insert(inst.foreign);
        }
        _ => {}
      }
    }
  }
  let mut out = free.into_iter().collect::<Vec<_>>();
  out.sort_by_key(|s| s.raw_id());
  out
}

impl Program {
  fn compile_with_lower(
    mut top_level_node: Node<TopLevel>,
    lower: LowerResult,
    top_level_mode: TopLevelMode,
    debug: bool,
  ) -> OptimizeResult<Self> {
    let (semantics, _) = JsSymbols::bind(&mut top_level_node, top_level_mode, SOURCE_FILE);
    let VarAnalysis {
      foreign,
      use_before_decl,
      dynamic_scope,
      ..
    } = VarAnalysis::analyze(&mut top_level_node, &semantics);
    if let Some(loc) = dynamic_scope {
      return Err(unsupported_syntax(
        loc,
        "with statements introduce dynamic scope and are not supported",
      ));
    }
    // SSA requires no use before declaration.
    if !use_before_decl.is_empty() {
      let mut diagnostics: Vec<_> = use_before_decl
        .into_iter()
        .map(|(_, (name, loc))| use_before_declaration(&name, loc))
        .collect();
      sort_diagnostics(&mut diagnostics);
      return Err(diagnostics);
    };
    let mut symbol_table = collect_symbol_table(&semantics, &foreign);

    let bindings = collect_hir_symbol_bindings(&mut top_level_node, &lower);
    let lower = Arc::new(lower);
    let program = ProgramCompiler(Arc::new(ProgramCompilerInner {
      foreign_vars: foreign.clone(),
      functions: DashMap::new(),
      next_fn_id: AtomicUsize::new(0),
      debug,
      lower: Arc::clone(&lower),
      bindings,
      names: Arc::clone(&lower.names),
    }));

    let top_level = compile_hir_body(&program, lower.root_body())?;
    let ProgramCompilerInner {
      functions,
      next_fn_id,
      ..
    } = Arc::try_unwrap(program.0).unwrap();
    let fn_count = next_fn_id.load(Ordering::Relaxed);
    let functions: Vec<_> = (0..fn_count)
      .map(|i| functions.remove(&i).unwrap().1)
      .collect();

    let free_symbols = ProgramFreeSymbols {
      top_level: collect_free_symbols(&top_level),
      functions: functions.iter().map(collect_free_symbols).collect(),
    };

    let has_any_symbols = !symbol_table.symbols.is_empty()
      || !free_symbols.top_level.is_empty()
      || free_symbols.functions.iter().any(|f| !f.is_empty());

    let symbols = if has_any_symbols {
      symbol_table.free_symbols = Some(free_symbols);
      Some(symbol_table)
    } else {
      None
    };

    Ok(Self {
      functions,
      top_level,
      top_level_mode,
      symbols,
    })
  }

  pub fn compile(
    top_level_node: Node<TopLevel>,
    top_level_mode: TopLevelMode,
    debug: bool,
  ) -> OptimizeResult<Self> {
    let lower = hir_js::lower_file(SOURCE_FILE, HirFileKind::Ts, &top_level_node);
    Self::compile_with_lower(top_level_node, lower, top_level_mode, debug)
  }

  pub fn compile_lowered(
    source: &str,
    lower: LowerResult,
    top_level_mode: TopLevelMode,
    debug: bool,
  ) -> OptimizeResult<Self> {
    let top_level_node = parse(source).map_err(|err| vec![err.to_diagnostic(SOURCE_FILE)])?;
    Self::compile_with_lower(top_level_node, lower, top_level_mode, debug)
  }
}

#[cfg(test)]
mod tests {
  use super::SOURCE_FILE;
  use crate::cfg::cfg::Cfg;
  use crate::compile_source;
  use crate::il::inst::Inst;
  use crate::il::inst::InstTyp;
  use crate::symbol::semantics::JsSymbols;
  use crate::symbol::var_analysis::VarAnalysis;
  use crate::Program;
  use crate::TopLevelMode;
  use parse_js::parse;
  use serde_json::to_string;
  use std::collections::HashSet;

  fn compile_with_debug_json(source: &str) -> String {
    let top_level_node = parse(source).expect("parse input");
    let Program { top_level, .. } =
      Program::compile(top_level_node, TopLevelMode::Module, true).expect("compile");
    let debug = top_level.debug.expect("debug enabled");
    to_string(&debug).expect("serialize debug output")
  }

  fn collect_insts(cfg: &Cfg) -> Vec<Inst> {
    let mut blocks: Vec<_> = cfg.bblocks.all().collect();
    blocks.sort_by_key(|(label, _)| *label);
    let mut insts = Vec::new();
    for (_, block) in blocks.into_iter() {
      insts.extend(block.iter().cloned());
    }
    insts
  }

  fn collect_all_insts(program: &Program) -> Vec<Inst> {
    let mut insts = collect_insts(&program.top_level.body);
    for func in &program.functions {
      insts.extend(collect_insts(&func.body));
    }
    insts
  }

  fn compile_with_mode(source: &str, mode: TopLevelMode) -> Program {
    let top_level_node = parse(source).expect("parse input");
    Program::compile(top_level_node, mode, false).expect("compile input")
  }

  #[test]
  fn program_records_top_level_mode() {
    let program = compile_source("var x = 1;", TopLevelMode::Global, false).expect("compile");
    assert_eq!(program.top_level_mode, TopLevelMode::Global);
  }

  #[test]
  fn test_compile_js_statements() {
    let source = r#"
      (() => {
        a?.b?.c;
        let x = 1;
        if (x) {
          g();
          x += Math.round(1.1);
          for (;;) {
            x += 1;
            setTimeout(() => {
              h(x);
            }, 1000);
          }
        }
        f(x);
      })();
    "#;
    let top_level_node = parse(source).expect("parse input");
    let _bblocks = Program::compile(top_level_node, TopLevelMode::Module, false)
      .expect("compile")
      .top_level;
  }

  #[test]
  fn test_use_before_declaration_error() {
    let source = "function demo(){ a; let a = 1; }";
    let top_level_node = parse(source).expect("parse input");
    let err = Program::compile(top_level_node, TopLevelMode::Module, false)
      .expect_err("expected use-before-decl error");
    assert_eq!(err.len(), 1);
    let diagnostic = &err[0];
    assert_eq!(diagnostic.code, "OPT0001");
    let range = diagnostic.primary.range;
    assert!(range.start < range.end);
    assert_eq!(&source[range.start as usize..range.end as usize], "a");
  }

  #[test]
  fn optimizer_debug_output_is_deterministic() {
    let source = r#"
      let x = 1;
      if (x > 0) {
        x = x + 1;
      } else {
        x = x - 1;
      }
      while (x < 3) {
        x += 1;
      }
      x += 2;
    "#;

    let first = compile_with_debug_json(source);
    let second = compile_with_debug_json(source);

    assert_eq!(first, second, "debug output should be deterministic");
  }

  #[test]
  fn captured_reads_and_writes_use_foreign_insts() {
    let source = r#"
      let runner = () => {
        let x = 0;
        const bump = () => {
          x = x + 1;
          (() => {
            x = x + 1;
            x;
          })();
          x;
        };
        bump();
      };

      runner();
    "#;

    let program = compile_with_mode(source, TopLevelMode::Module);
    let insts = collect_all_insts(&program);

    let mut loads = HashSet::new();
    let mut stores = HashSet::new();
    for inst in insts {
      match inst.t {
        InstTyp::ForeignLoad => {
          loads.insert(inst.as_foreign_load().1);
        }
        InstTyp::ForeignStore => {
          stores.insert(inst.as_foreign_store().0);
        }
        _ => {}
      }
    }

    assert!(!loads.is_empty());
    assert!(!stores.is_empty());
    assert!(loads.intersection(&stores).next().is_some());
  }

  #[test]
  fn destructuring_declares_locals() {
    let source = r#"
      let {a} = obj;
      a = a + 1;
      call_me(a);
    "#;

    let mut top_level_node = parse(source).expect("parse input");
    let (symbols, _) = JsSymbols::bind(&mut top_level_node, TopLevelMode::Module, SOURCE_FILE);
    let analysis = VarAnalysis::analyze(&mut top_level_node, &symbols);
    assert_eq!(analysis.declared.len(), 1);
    assert!(analysis.unknown.contains("obj"));
    assert!(analysis.unknown.contains("call_me"));
    assert!(!analysis.unknown.contains("a"));

    let program =
      Program::compile(top_level_node, TopLevelMode::Module, false).expect("compile input");
    let insts = collect_all_insts(&program);

    #[cfg(test)]
    for inst in insts.iter() {
      if matches!(inst.t, InstTyp::UnknownLoad | InstTyp::UnknownStore) {
        eprintln!("unknown inst: {:?}", inst);
      }
    }
    assert!(insts.iter().all(|i| i.t != InstTyp::UnknownStore));
    let unknown_names: HashSet<_> = insts
      .iter()
      .filter(|i| matches!(i.t, InstTyp::UnknownLoad | InstTyp::UnknownStore))
      .map(|i| i.unknown.clone())
      .collect();
    assert!(!unknown_names.contains("a"));
  }

  #[test]
  fn global_mode_uses_unknown_memory_ops() {
    let source = r#"
      var a = 1;
      a = a + 2;
    "#;

    let program = compile_with_mode(source, TopLevelMode::Global);
    let insts = collect_insts(&program.top_level.body);

    assert!(insts.iter().any(|i| i.t == InstTyp::UnknownStore));
    assert!(insts.iter().any(|i| i.t == InstTyp::UnknownLoad));
  }

  #[test]
  fn optional_chaining_assignment_target_is_rejected() {
    let source = "a?.b = 1;";
    let top_level_node = parse(source).expect("parse input");
    let err =
      Program::compile(top_level_node, TopLevelMode::Module, false).expect_err("expected error");
    assert_eq!(err.len(), 1);
    assert_eq!(err[0].code, "OPT0002");
    assert!(err[0]
      .message
      .contains("optional chaining in assignment target"));
  }
}
