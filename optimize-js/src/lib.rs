pub mod analysis;
pub mod cfg;
pub mod dom;
pub mod eval;
pub mod graph;
pub mod il;
pub mod opt;
pub mod ssa;
pub mod symbol;
pub mod util;

use ahash::HashSet;
use analysis::defs::calculate_defs;
use cfg::bblock::convert_insts_to_bblocks;
use cfg::cfg::Cfg;
use dashmap::DashMap;
use dom::Dom;
use opt::optpass_cfg_prune::optpass_cfg_prune;
use opt::optpass_dvn::optpass_dvn;
use opt::optpass_impossible_branches::optpass_impossible_branches;
use opt::optpass_redundant_assigns::optpass_redundant_assigns;
use opt::optpass_trivial_dce::optpass_trivial_dce;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use parse_js::parse;
use serde::Serialize;
use ssa::ssa_deconstruct::deconstruct_ssa;
use ssa::ssa_insert_phis::insert_phis_for_ssa_construction;
use ssa::ssa_rename::rename_targets_for_ssa_construction;
use std::ops::Deref;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use symbol::var_analysis::VarAnalysis;
use symbol_js::compute_symbols;
use symbol_js::symbol::Scope;
use symbol_js::symbol::Symbol;
pub use symbol_js::TopLevelMode;
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ScopeId(pub u32);

#[derive(Debug, Serialize)]
pub struct ProgramSymbol {
  pub id: Symbol,
  pub name: String,
  pub scope: ScopeId,
  pub captured: bool,
}

#[derive(Debug, Serialize)]
pub struct ProgramFreeSymbols {
  pub top_level: Vec<Symbol>,
  pub functions: Vec<Vec<Symbol>>, // Index aligned with Program::functions.
}

#[derive(Debug, Serialize)]
pub struct ProgramSymbols {
  pub symbols: Vec<ProgramSymbol>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub free_symbols: Option<ProgramFreeSymbols>,
}

pub fn compile_js_statements(
  program: &ProgramCompiler,
  statements: Vec<Node<Stmt>>,
) -> OptimizeResult<ProgramFunction> {
  let mut dbg = program.debug.then(|| OptimizerDebug::new());
  let mut dbg_checkpoint = |name: &str, cfg: &Cfg| {
    dbg.as_mut().map(|dbg| dbg.add_step(name, cfg));
  };

  let (insts, mut c_label, mut c_temp) = program.translate_source_to_inst(statements)?;
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

  Ok(ProgramFunction {
    debug: dbg,
    body: cfg,
  })
}

pub type FnId = usize;

#[derive(Debug)]
pub struct ProgramCompilerInner {
  // Precomputed via VarAnalysis.
  pub foreign_vars: HashSet<Symbol>,
  pub functions: DashMap<FnId, ProgramFunction>,
  pub next_fn_id: AtomicUsize,
  pub debug: bool,
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

#[derive(Debug)]
pub struct Program {
  pub functions: Vec<ProgramFunction>,
  pub top_level: ProgramFunction,
  pub symbols: Option<ProgramSymbols>,
}

/// Parse, symbolize, and compile source text in one step.
pub fn compile_source(source: &str, mode: TopLevelMode, debug: bool) -> OptimizeResult<Program> {
  let mut top_level_node = parse(source).map_err(|err| vec![err.to_diagnostic(SOURCE_FILE)])?;
  compute_symbols(&mut top_level_node, mode);
  Program::compile(top_level_node, debug)
}

fn collect_symbol_table(root: &Scope, captured: &HashSet<Symbol>) -> ProgramSymbols {
  fn collect_scope_symbols(
    scope: &Scope,
    scope_id: &mut u32,
    captured: &HashSet<Symbol>,
    out: &mut Vec<ProgramSymbol>,
  ) {
    let this_scope_id = ScopeId(*scope_id);
    *scope_id += 1;

    let (symbols, children) = {
      let data = scope.data();
      let symbols = data
        .symbol_names()
        .iter()
        .map(|name| (name.clone(), data.get_symbol(name).unwrap()))
        .collect::<Vec<_>>();
      let children = data.children().clone();
      (symbols, children)
    };

    for (name, id) in symbols {
      out.push(ProgramSymbol {
        id,
        name,
        scope: this_scope_id,
        captured: captured.contains(&id),
      });
    }

    for child in children {
      collect_scope_symbols(&child, scope_id, captured, out);
    }
  }

  let mut symbols = Vec::new();
  collect_scope_symbols(root, &mut 0, captured, &mut symbols);
  ProgramSymbols {
    symbols,
    free_symbols: None,
  }
}

fn collect_free_symbols(func: &ProgramFunction) -> Vec<Symbol> {
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
  // The AST must already have symbol analysis done by compute_symbols.
  pub fn compile(mut top_level_node: Node<TopLevel>, debug: bool) -> OptimizeResult<Self> {
    let VarAnalysis {
      foreign,
      use_before_decl,
      ..
    } = VarAnalysis::analyze(&mut top_level_node);
    // SSA requires no use before declaration.
    if !use_before_decl.is_empty() {
      let mut diagnostics: Vec<_> = use_before_decl
        .into_iter()
        .map(|(_, (name, loc))| use_before_declaration(&name, loc))
        .collect();
      sort_diagnostics(&mut diagnostics);
      return Err(diagnostics);
    };
    let symbol_table = top_level_node
      .assoc
      .get::<Scope>()
      .map(|scope| collect_symbol_table(scope, &foreign));

    let TopLevel { body } = *top_level_node.stx;
    let program = ProgramCompiler(Arc::new(ProgramCompilerInner {
      foreign_vars: foreign,
      functions: DashMap::new(),
      next_fn_id: AtomicUsize::new(0),
      debug,
    }));
    let top_level = compile_js_statements(&program, body)?;
    let ProgramCompilerInner {
      functions,
      next_fn_id,
      ..
    } = Arc::try_unwrap(program.0).unwrap();
    let fn_count = next_fn_id.load(Ordering::Relaxed);
    let functions: Vec<_> = (0..fn_count)
      .map(|i| functions.remove(&i).unwrap().1)
      .collect();

    let free_symbols = symbol_table.as_ref().map(|_| ProgramFreeSymbols {
      top_level: collect_free_symbols(&top_level),
      functions: functions.iter().map(collect_free_symbols).collect(),
    });

    if let (Some(sym), Some(free)) = (symbol_table.as_ref(), free_symbols.as_ref()) {
      if sym.symbols.is_empty()
        && free.top_level.is_empty()
        && free.functions.iter().all(|f| f.is_empty())
      {
        return Ok(Self {
          functions,
          top_level,
          symbols: None,
        });
      }
    }

    Ok(Self {
      functions,
      top_level,
      symbols: symbol_table.map(|mut table| {
        table.free_symbols = free_symbols;
        table
      }),
    })
  }
}

#[cfg(test)]
mod tests {
  use crate::cfg::cfg::Cfg;
  use crate::il::inst::Inst;
  use crate::il::inst::InstTyp;
  use crate::symbol::var_analysis::VarAnalysis;
  use crate::Program;
  use parse_js::parse;
  use serde_json::to_string;
  use std::collections::HashSet;
  use symbol_js::compute_symbols;
  use symbol_js::TopLevelMode;

  fn compile_with_debug_json(source: &str) -> String {
    let mut top_level_node = parse(source).expect("parse input");
    compute_symbols(&mut top_level_node, TopLevelMode::Module);
    let Program { top_level, .. } = Program::compile(top_level_node, true).expect("compile");
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
    let mut top_level_node = parse(source).expect("parse input");
    compute_symbols(&mut top_level_node, mode);
    Program::compile(top_level_node, false).expect("compile input")
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
    let mut top_level_node = parse(source).expect("parse input");
    compute_symbols(&mut top_level_node, TopLevelMode::Module);
    let _bblocks = Program::compile(top_level_node, false)
      .expect("compile")
      .top_level;
  }

  #[test]
  fn test_use_before_declaration_error() {
    let source = "function demo(){ a; let a = 1; }";
    let mut top_level_node = parse(source).expect("parse input");
    compute_symbols(&mut top_level_node, TopLevelMode::Module);
    let err = Program::compile(top_level_node, false).expect_err("expected use-before-decl error");
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
    compute_symbols(&mut top_level_node, TopLevelMode::Module);
    let analysis = VarAnalysis::analyze(&mut top_level_node);
    assert_eq!(analysis.declared.len(), 1);
    assert!(analysis.unknown.contains("obj"));
    assert!(analysis.unknown.contains("call_me"));
    assert!(!analysis.unknown.contains("a"));

    let program = Program::compile(top_level_node, false).expect("compile input");
    let insts = collect_all_insts(&program);

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
    let mut top_level_node = parse(source).expect("parse input");
    compute_symbols(&mut top_level_node, TopLevelMode::Module);
    let err = Program::compile(top_level_node, false).expect_err("expected error");
    assert_eq!(err.len(), 1);
    assert_eq!(err[0].code, "OPT0002");
    assert!(err[0]
      .message
      .contains("optional chaining in assignment target"));
  }
}
