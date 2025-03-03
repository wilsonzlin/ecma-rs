pub mod cfg;
pub mod graph;
pub mod dom;
pub mod opt;
pub mod ssa;
pub mod symbol;
pub mod il;
pub mod util;
pub mod eval;
pub mod analysis;

use std::{ops::Deref, sync::{atomic::{AtomicUsize, Ordering}, Arc}};

use ahash::HashSet;
use analysis::defs::calculate_defs;
use cfg::{bblock::convert_insts_to_bblocks, cfg::Cfg};
use crossbeam_utils::sync::WaitGroup;
use dashmap::DashMap;
use dom::Dom;
use opt::{optpass_cfg_prune::optpass_cfg_prune, optpass_dvn::optpass_dvn, optpass_impossible_branches::optpass_impossible_branches, optpass_redundant_assigns::optpass_redundant_assigns, optpass_trivial_dce::optpass_trivial_dce};
use parse_js::ast::{stmt::Stmt, stx::TopLevel};
use serde::Serialize;
use parse_js::ast::node::Node;
use ssa::{ssa_deconstruct::deconstruct_ssa, ssa_insert_phis::insert_phis_for_ssa_construction, ssa_rename::rename_targets_for_ssa_construction};
use symbol::var_analysis::VarAnalysis;
use symbol_js::symbol::Symbol;
use util::{counter::Counter, debug::OptimizerDebug};

// The top level is considered a function (the optimizer concept, not parser or symbolizer).
#[derive(Debug, Serialize)]
pub struct ProgramFunction {
  pub debug: Option<OptimizerDebug>,
  pub body: Cfg,
}

pub fn compile_js_statements(
  program: &ProgramCompiler,
  statements: Vec<Node<Stmt>>,
) -> ProgramFunction {
  let mut dbg = program.debug.then(|| OptimizerDebug::new());
  let mut dbg_checkpoint = |name: &str, cfg: &Cfg| {
    dbg.as_mut().map(|dbg| dbg.add_step(name, cfg));
  };

  let (insts, mut c_label, mut c_temp) = program.translate_source_to_inst(statements);
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

pub struct Program {
  pub functions: Vec<ProgramFunction>,
  pub top_level: ProgramFunction,
}

impl Program {
  // The AST must already have symbol analysis done by compute_symbols.
  pub fn compile(top_level_node: Node<TopLevel>, debug: bool) -> Self {
    let VarAnalysis {
      declared,
      foreign,
      unknown,
      use_before_decl,
    } = VarAnalysis::analyze(&top_level_node);
    // SSA requires no use before declaration.
    if let Some((_, loc)) = use_before_decl.iter().next() {
      panic!("Use before declaration at {:?}", loc);
    };
    let TopLevel { body } = *top_level_node.stx;
    let program = ProgramCompiler(Arc::new(ProgramCompilerInner {
      foreign_vars: foreign,
      functions: DashMap::new(),
      next_fn_id: AtomicUsize::new(0),
      debug,
    }));
    let top_level = compile_js_statements(&program, body);
    let ProgramCompilerInner {
      functions,
      next_fn_id,
      ..
    } = Arc::try_unwrap(program.0).unwrap();
    let fn_count = next_fn_id.load(Ordering::Relaxed);
    Self {
      functions: (0..fn_count).map(|i| functions.remove(&i).unwrap().1).collect(),
      top_level,
    }
  }
}

#[cfg(test)]
mod tests {
    use parse_js::parse;
    use symbol_js::{compute_symbols, TopLevelMode};

    use crate::Program;

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
    let mut top_level_node = parse(source.as_bytes()).expect("parse input");
    compute_symbols(&mut top_level_node, TopLevelMode::Module);
    let bblocks = Program::compile(top_level_node, false).top_level;
  }
}
