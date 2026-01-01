use diagnostics::FileId;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use semantic_js::js::{bind_js, JsSemantics, ScopeId, TopLevelMode};
use std::collections::BTreeSet;
use std::fmt;

use crate::rename::collect_usages;
use crate::rename::UsageData;

mod cleanup;
mod const_fold;
mod dce;
mod sem_rewrite;
mod side_effects;
mod stmt_rewrite;
mod traverse;

pub(crate) fn optimize(file: FileId, top_level_mode: TopLevelMode, top: &mut Node<TopLevel>) {
  let mut cx = OptCtx::new(file, top_level_mode);

  let mut pre = PassPipeline::new(vec![
    Box::new(const_fold::ConstFoldPass),
    Box::new(stmt_rewrite::StmtRewritePass),
    Box::new(cleanup::CleanupPass),
  ]);
  pre.run(&mut cx, top, 4);

  // Post-bind passes may create new identifier nodes (e.g. semantic rewrites) or
  // remove declarations (DCE). Re-bind at the start of each iteration so
  // subsequent passes always operate on up-to-date scope/symbol associations.
  let mut post = PassPipeline::new(vec![
    Box::new(dce::DcePass),
    Box::new(sem_rewrite::SemanticRewritePass),
    Box::new(cleanup::CleanupPass),
  ]);
  for _ in 0..2 {
    cx.bind(top);
    let mut changed = false;
    for pass in post.passes.iter_mut() {
      changed |= pass.run(&mut cx, top);
    }
    if !changed {
      break;
    }
  }
}

struct OptCtx {
  file: FileId,
  top_level_mode: TopLevelMode,
  sem: Option<JsSemantics>,
  usage: Option<UsageData>,
  disabled_scopes: BTreeSet<ScopeId>,
}

impl OptCtx {
  fn new(file: FileId, top_level_mode: TopLevelMode) -> Self {
    Self {
      file,
      top_level_mode,
      sem: None,
      usage: None,
      disabled_scopes: BTreeSet::new(),
    }
  }

  fn bind(&mut self, top: &mut Node<TopLevel>) {
    let (sem, _) = bind_js(top, self.top_level_mode, self.file);
    let usage = collect_usages(top, &sem, self.top_level_mode);
    let disabled_scopes = compute_disabled_scopes(&sem, &usage);
    self.sem = Some(sem);
    self.usage = Some(usage);
    self.disabled_scopes = disabled_scopes;
  }

  fn sem(&self) -> &JsSemantics {
    self.sem.as_ref().expect("semantics must be initialized")
  }

  fn usage(&self) -> &UsageData {
    self.usage.as_ref().expect("usage data must be initialized")
  }
}

fn compute_disabled_scopes(sem: &JsSemantics, usage: &UsageData) -> BTreeSet<ScopeId> {
  let mut disabled = BTreeSet::new();
  for (scope, hazards) in usage.scope_hazards.iter() {
    if hazards.has_with || hazards.has_direct_eval {
      disabled.insert(*scope);
    }
    if hazards.has_direct_eval {
      let mut current = sem.scope(*scope).parent;
      while let Some(scope_id) = current {
        disabled.insert(scope_id);
        current = sem.scope(scope_id).parent;
      }
    }
  }
  disabled
}

trait Pass {
  fn name(&self) -> &'static str;
  fn run(&mut self, cx: &mut OptCtx, top: &mut Node<TopLevel>) -> bool;
}

struct PassPipeline {
  passes: Vec<Box<dyn Pass>>,
}

impl PassPipeline {
  fn new(passes: Vec<Box<dyn Pass>>) -> Self {
    Self { passes }
  }

  fn run(&mut self, cx: &mut OptCtx, top: &mut Node<TopLevel>, max_iters: usize) {
    for _ in 0..max_iters {
      let mut changed = false;
      for pass in self.passes.iter_mut() {
        changed |= pass.run(cx, top);
      }
      if !changed {
        break;
      }
    }
  }
}

impl fmt::Debug for PassPipeline {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("PassPipeline")
      .field(
        "passes",
        &self.passes.iter().map(|p| p.name()).collect::<Vec<_>>(),
      )
      .finish()
  }
}
