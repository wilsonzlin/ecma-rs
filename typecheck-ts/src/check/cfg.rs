//! Minimal control-flow graph representation for TypeScript bodies built on top
//! of `hir-js`.
//!
//! The CFG deliberately operates at the statement level, producing one basic
//! block per [`StmtId`] and wiring edges for the common control-flow constructs
//! used by the lightweight checker (conditionals, switches, and loops).

use hir_js::hir::{CatchClause, SwitchCase};
use hir_js::{Body, ExprId, ForInit, NameId, StmtId, StmtKind};
use std::collections::HashSet;
use std::fmt;

/// Identifier for a basic block inside a body-local CFG.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct BlockId(pub usize);

/// Directed edge between two blocks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Edge {
  pub from: BlockId,
  pub to: BlockId,
}

/// Minimal basic block containing a list of statement indices.
#[derive(Clone, Debug, Default)]
pub struct BasicBlock {
  pub id: BlockId,
  pub kind: BlockKind,
  pub stmts: Vec<StmtId>,
  pub successors: Vec<BlockId>,
}

/// Specialized actions performed on entry to a block before executing any
/// contained statements.
#[derive(Clone, Debug, PartialEq)]
pub enum BlockKind {
  /// Standard block that only executes its statements.
  Normal,
  /// `for` initializer executed once before entering the loop test.
  ForInit { init: Option<ForInit> },
  /// `for` test that branches to the body (true) or after the loop (false).
  ForTest { test: Option<ExprId> },
  /// `for` update executed at the end of each iteration.
  ForUpdate { update: Option<ExprId> },
  /// `do...while` test executed after the body.
  DoWhileTest { test: ExprId },
}

impl Default for BlockKind {
  fn default() -> Self {
    BlockKind::Normal
  }
}

/// Control-flow graph with entry/exit blocks.
#[derive(Clone, Debug, Default)]
pub struct ControlFlowGraph {
  pub entry: BlockId,
  pub exit: BlockId,
  pub blocks: Vec<BasicBlock>,
}

impl ControlFlowGraph {
  /// Create a new CFG with a single empty entry/exit block.
  pub fn new() -> Self {
    ControlFlowGraph {
      entry: BlockId(0),
      exit: BlockId(0),
      blocks: Vec::new(),
    }
  }

  /// Add a new block, returning its identifier.
  pub fn add_block(&mut self) -> BlockId {
    let id = BlockId(self.blocks.len());
    self.blocks.push(BasicBlock {
      id,
      ..Default::default()
    });
    id
  }

  /// Add a directed edge between two blocks.
  pub fn add_edge(&mut self, from: BlockId, to: BlockId) {
    if let Some(block) = self.blocks.get_mut(from.0) {
      block.successors.push(to);
    }
  }

  /// Build a control-flow graph for a HIR [`Body`], creating one block per
  /// statement plus dedicated entry/exit blocks.
  pub fn from_body(body: &Body) -> ControlFlowGraph {
    let builder = CfgBuilder::new(body);
    builder.build()
  }
}

impl fmt::Display for ControlFlowGraph {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(
      f,
      "CFG(entry={:?}, exit={:?}, blocks={})",
      self.entry,
      self.exit,
      self.blocks.len()
    )?;
    for block in &self.blocks {
      writeln!(
        f,
        "  {:?}: kind={:?} stmts={:?} succ={:?}",
        block.id, block.kind, block.stmts, block.successors
      )?;
    }
    Ok(())
  }
}

/// Internal CFG builder that walks statement lists recursively.
struct CfgBuilder<'a> {
  cfg: ControlFlowGraph,
  body: &'a Body,
  breakables: Vec<BreakableContext>,
}

#[derive(Default)]
struct BuildResult {
  entry: Option<BlockId>,
  exits: Vec<BlockId>,
}

#[derive(Clone, Copy, Debug)]
struct BreakableContext {
  label: Option<NameId>,
  break_target: BlockId,
  continue_target: Option<BlockId>,
  /// Whether an unlabeled `break` can target this construct.
  implicit_break: bool,
}

impl<'a> CfgBuilder<'a> {
  fn new(body: &'a Body) -> Self {
    let mut cfg = ControlFlowGraph::new();
    let entry = cfg.add_block();
    let exit = cfg.add_block();
    cfg.entry = entry;
    cfg.exit = exit;
    Self {
      cfg,
      body,
      breakables: Vec::new(),
    }
  }

  fn build(mut self) -> ControlFlowGraph {
    let roots = self.root_stmts();
    if roots.is_empty() {
      self.cfg.add_edge(self.cfg.entry, self.cfg.exit);
      return self.cfg;
    }

    let mut preds = vec![self.cfg.entry];
    for stmt in roots {
      let res = self.build_stmt(stmt, preds);
      preds = res.exits;
    }

    if !preds.is_empty() {
      self.connect(&preds, self.cfg.exit);
    }
    self.cfg
  }

  fn connect(&mut self, from: &[BlockId], to: BlockId) {
    for pred in from {
      self.cfg.add_edge(*pred, to);
    }
  }

  fn root_stmts(&self) -> Vec<StmtId> {
    if !self.body.root_stmts.is_empty() {
      return self.body.root_stmts.clone();
    }
    let mut referenced: HashSet<StmtId> = HashSet::new();
    for stmt in self.body.stmts.iter() {
      referenced.extend(child_stmt_ids(stmt));
    }
    let mut roots: Vec<StmtId> = (0..self.body.stmts.len() as u32)
      .map(StmtId)
      .filter(|id| !referenced.contains(id))
      .collect();
    roots.sort_by_key(|id| id.0);
    roots
  }

  fn add_stmt_block(&mut self, stmt_id: StmtId) -> BlockId {
    let block = self.cfg.add_block();
    self.cfg.blocks[block.0].stmts.push(stmt_id);
    block
  }

  fn resolve_break_target(&self, label: Option<NameId>) -> Option<BlockId> {
    if let Some(label) = label {
      self
        .breakables
        .iter()
        .rev()
        .find(|ctx| ctx.label == Some(label))
        .map(|ctx| ctx.break_target)
    } else {
      self
        .breakables
        .iter()
        .rev()
        .find(|ctx| ctx.implicit_break)
        .map(|ctx| ctx.break_target)
    }
  }

  fn resolve_continue_target(&self, label: Option<NameId>) -> Option<BlockId> {
    if let Some(label) = label {
      self
        .breakables
        .iter()
        .rev()
        .find(|ctx| ctx.label == Some(label) && ctx.continue_target.is_some())
        .and_then(|ctx| ctx.continue_target)
    } else {
      self
        .breakables
        .iter()
        .rev()
        .find_map(|ctx| ctx.continue_target)
    }
  }

  fn build_stmt_list(&mut self, stmts: &[StmtId], mut preds: Vec<BlockId>) -> BuildResult {
    let mut entry = None;
    for stmt in stmts {
      let res = self.build_stmt(*stmt, preds);
      if entry.is_none() {
        entry = res.entry;
      }
      preds = res.exits;
    }
    BuildResult {
      entry,
      exits: preds,
    }
  }

  fn build_stmt(&mut self, stmt_id: StmtId, preds: Vec<BlockId>) -> BuildResult {
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    match &stmt.kind {
      StmtKind::If {
        consequent,
        alternate,
        ..
      } => self.build_if(stmt_id, *consequent, alternate.as_ref(), preds),
      StmtKind::Switch { cases, .. } => self.build_switch(stmt_id, cases, preds, None),
      StmtKind::While { body, .. } => self.build_while(stmt_id, *body, preds, None),
      StmtKind::DoWhile { body, test } => self.build_do_while(stmt_id, *body, *test, preds, None),
      StmtKind::For {
        body,
        init,
        test,
        update,
      } => self.build_for(stmt_id, *body, init.clone(), *test, *update, preds, None),
      StmtKind::ForIn { body, .. } => self.build_for_in(stmt_id, *body, preds, None),
      StmtKind::Block(stmts) => {
        let block = self.add_stmt_block(stmt_id);
        self.connect(&preds, block);
        if stmts.is_empty() {
          BuildResult {
            entry: Some(block),
            exits: vec![block],
          }
        } else {
          let inner = self.build_stmt_list(stmts, vec![block]);
          BuildResult {
            entry: Some(block),
            exits: inner.exits,
          }
        }
      }
      StmtKind::Try {
        block: inner,
        catch,
        finally_block,
      } => self.build_try(
        stmt_id,
        *inner,
        catch.as_ref(),
        finally_block.as_ref(),
        preds,
      ),
      StmtKind::Return(_) | StmtKind::Throw(_) => {
        let block = self.add_stmt_block(stmt_id);
        self.connect(&preds, block);
        BuildResult {
          entry: Some(block),
          exits: Vec::new(),
        }
      }
      StmtKind::Break(label) => {
        let block = self.add_stmt_block(stmt_id);
        self.connect(&preds, block);
        if let Some(target) = self.resolve_break_target(*label) {
          self.cfg.add_edge(block, target);
        }
        BuildResult {
          entry: Some(block),
          exits: Vec::new(),
        }
      }
      StmtKind::Continue(label) => {
        let block = self.add_stmt_block(stmt_id);
        self.connect(&preds, block);
        if let Some(target) = self.resolve_continue_target(*label) {
          self.cfg.add_edge(block, target);
        }
        BuildResult {
          entry: Some(block),
          exits: Vec::new(),
        }
      }
      StmtKind::Var(_) | StmtKind::Decl(_) | StmtKind::Expr(_) | StmtKind::Empty => {
        let block = self.add_stmt_block(stmt_id);
        self.connect(&preds, block);
        BuildResult {
          entry: Some(block),
          exits: vec![block],
        }
      }
      StmtKind::Labeled { label, body } => self.build_labeled(stmt_id, *label, *body, preds),
      StmtKind::With { body, .. } => {
        let block = self.add_stmt_block(stmt_id);
        self.connect(&preds, block);
        let inner = self.build_stmt(*body, vec![block]);
        BuildResult {
          entry: Some(block),
          exits: inner.exits,
        }
      }
    }
  }

  fn build_if(
    &mut self,
    stmt_id: StmtId,
    consequent: StmtId,
    alternate: Option<&StmtId>,
    preds: Vec<BlockId>,
  ) -> BuildResult {
    let cond_block = self.add_stmt_block(stmt_id);
    self.connect(&preds, cond_block);
    let after = self.cfg.add_block();

    let then_res = self.build_stmt(consequent, vec![cond_block]);
    self.connect(&then_res.exits, after);

    if let Some(alt) = alternate {
      let else_res = self.build_stmt(*alt, vec![cond_block]);
      self.connect(&else_res.exits, after);
    } else {
      self.cfg.add_edge(cond_block, after);
    }

    BuildResult {
      entry: Some(cond_block),
      exits: vec![after],
    }
  }

  fn build_switch(
    &mut self,
    stmt_id: StmtId,
    cases: &[SwitchCase],
    preds: Vec<BlockId>,
    label: Option<NameId>,
  ) -> BuildResult {
    let block = self.add_stmt_block(stmt_id);
    self.connect(&preds, block);

    let after = self.cfg.add_block();
    self.breakables.push(BreakableContext {
      label,
      break_target: after,
      continue_target: None,
      implicit_break: true,
    });

    let mut has_default = false;
    let mut case_entries: Vec<BlockId> = Vec::with_capacity(cases.len());
    let mut next_entry = after;
    for case in cases.iter().rev() {
      if case.test.is_none() {
        has_default = true;
      }
      let entry = if case.consequent.is_empty() {
        next_entry
      } else {
        let res = self.build_stmt_list(&case.consequent, Vec::new());
        if !res.exits.is_empty() {
          self.connect(&res.exits, next_entry);
        }
        res.entry.unwrap_or(next_entry)
      };
      case_entries.push(entry);
      next_entry = entry;
    }
    self.breakables.pop();

    case_entries.reverse();
    for entry in &case_entries {
      self.cfg.add_edge(block, *entry);
    }
    if !has_default {
      self.cfg.add_edge(block, after);
    }

    BuildResult {
      entry: Some(block),
      exits: vec![after],
    }
  }

  fn build_while(
    &mut self,
    stmt_id: StmtId,
    body: StmtId,
    preds: Vec<BlockId>,
    label: Option<NameId>,
  ) -> BuildResult {
    let header = self.add_stmt_block(stmt_id);
    self.connect(&preds, header);

    let after = self.cfg.add_block();
    self.breakables.push(BreakableContext {
      label,
      break_target: after,
      continue_target: Some(header),
      implicit_break: true,
    });
    let body_res = self.build_stmt(body, vec![header]);
    self.connect(&body_res.exits, header);
    self.breakables.pop();

    self.cfg.add_edge(header, after);

    BuildResult {
      entry: Some(header),
      exits: vec![after],
    }
  }

  fn build_do_while(
    &mut self,
    stmt_id: StmtId,
    body: StmtId,
    test: ExprId,
    preds: Vec<BlockId>,
    label: Option<NameId>,
  ) -> BuildResult {
    let after = self.cfg.add_block();
    let test_block = self.add_stmt_block(stmt_id);
    self.cfg.blocks[test_block.0].kind = BlockKind::DoWhileTest { test };
    self.breakables.push(BreakableContext {
      label,
      break_target: after,
      continue_target: Some(test_block),
      implicit_break: true,
    });
    let body_res = self.build_stmt(body, preds);
    self.connect(&body_res.exits, test_block);
    self.breakables.pop();

    if let Some(entry) = body_res.entry {
      self.cfg.add_edge(test_block, entry);
    }
    self.cfg.add_edge(test_block, after);

    BuildResult {
      entry: body_res.entry.or(Some(test_block)),
      exits: vec![after],
    }
  }

  fn build_for(
    &mut self,
    stmt_id: StmtId,
    body: StmtId,
    init: Option<ForInit>,
    test: Option<ExprId>,
    update: Option<ExprId>,
    preds: Vec<BlockId>,
    label: Option<NameId>,
  ) -> BuildResult {
    let init_block = self.cfg.add_block();
    self.cfg.blocks[init_block.0].kind = BlockKind::ForInit { init };
    self.connect(&preds, init_block);

    let test_block = self.cfg.add_block();
    self.cfg.blocks[test_block.0].kind = BlockKind::ForTest { test };
    self.cfg.blocks[test_block.0].stmts.push(stmt_id);

    let update_block = self.cfg.add_block();
    self.cfg.blocks[update_block.0].kind = BlockKind::ForUpdate { update };
    self.cfg.add_edge(update_block, test_block);

    let after = self.cfg.add_block();
    self.breakables.push(BreakableContext {
      label,
      break_target: after,
      continue_target: Some(update_block),
      implicit_break: true,
    });
    let body_res = self.build_stmt(body, vec![test_block]);
    self.connect(&body_res.exits, update_block);
    self.breakables.pop();

    if let Some(entry) = body_res.entry {
      self.cfg.add_edge(test_block, entry);
    }
    self.cfg.add_edge(init_block, test_block);
    self.cfg.add_edge(test_block, after);

    BuildResult {
      entry: Some(init_block),
      exits: vec![after],
    }
  }

  fn build_for_in(
    &mut self,
    stmt_id: StmtId,
    body: StmtId,
    preds: Vec<BlockId>,
    label: Option<NameId>,
  ) -> BuildResult {
    let header = self.add_stmt_block(stmt_id);
    self.connect(&preds, header);

    let after = self.cfg.add_block();
    self.breakables.push(BreakableContext {
      label,
      break_target: after,
      continue_target: Some(header),
      implicit_break: true,
    });
    let body_res = self.build_stmt(body, vec![header]);
    self.connect(&body_res.exits, header);
    self.breakables.pop();

    self.cfg.add_edge(header, after);

    BuildResult {
      entry: Some(header),
      exits: vec![after],
    }
  }

  fn build_try(
    &mut self,
    stmt_id: StmtId,
    inner: StmtId,
    catch: Option<&CatchClause>,
    finally_block: Option<&StmtId>,
    preds: Vec<BlockId>,
  ) -> BuildResult {
    let block = self.add_stmt_block(stmt_id);
    self.connect(&preds, block);

    let after = self.cfg.add_block();
    let mut exits = Vec::new();

    let try_res = self.build_stmt(inner, vec![block]);
    exits.extend(try_res.exits);

    if let Some(c) = catch {
      let catch_res = self.build_stmt(c.body, vec![block]);
      exits.extend(catch_res.exits);
    }

    if let Some(finally_stmt) = finally_block {
      let finally_res = self.build_stmt(*finally_stmt, exits);
      self.connect(&finally_res.exits, after);
    } else {
      self.connect(&exits, after);
    }

    BuildResult {
      entry: Some(block),
      exits: vec![after],
    }
  }

  fn build_labeled(
    &mut self,
    stmt_id: StmtId,
    label: NameId,
    body_id: StmtId,
    preds: Vec<BlockId>,
  ) -> BuildResult {
    let label_block = self.add_stmt_block(stmt_id);
    self.connect(&preds, label_block);
    let body_stmt = &self.body.stmts[body_id.0 as usize];
    let body_res = match &body_stmt.kind {
      StmtKind::While { body, .. } => {
        self.build_while(body_id, *body, vec![label_block], Some(label))
      }
      StmtKind::DoWhile { body, test, .. } => {
        self.build_do_while(body_id, *body, *test, vec![label_block], Some(label))
      }
      StmtKind::For {
        body,
        init,
        test,
        update,
        ..
      } => self.build_for(
        body_id,
        *body,
        init.clone(),
        *test,
        *update,
        vec![label_block],
        Some(label),
      ),
      StmtKind::ForIn { body, .. } => {
        self.build_for_in(body_id, *body, vec![label_block], Some(label))
      }
      StmtKind::Switch { cases, .. } => {
        self.build_switch(body_id, cases, vec![label_block], Some(label))
      }
      _ => {
        let after = self.cfg.add_block();
        self.breakables.push(BreakableContext {
          label: Some(label),
          break_target: after,
          continue_target: None,
          implicit_break: false,
        });
        let inner = self.build_stmt(body_id, vec![label_block]);
        self.connect(&inner.exits, after);
        self.breakables.pop();
        BuildResult {
          entry: Some(label_block),
          exits: vec![after],
        }
      }
    };

    BuildResult {
      entry: Some(label_block),
      exits: body_res.exits,
    }
  }
}

fn child_stmt_ids(stmt: &hir_js::Stmt) -> Vec<StmtId> {
  match &stmt.kind {
    StmtKind::Block(stmts) => stmts.clone(),
    StmtKind::If {
      consequent,
      alternate,
      ..
    } => alternate
      .iter()
      .copied()
      .chain(std::iter::once(*consequent))
      .collect(),
    StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } => vec![*body],
    StmtKind::For { body, .. } => vec![*body],
    StmtKind::ForIn { body, .. } => vec![*body],
    StmtKind::Switch { cases, .. } => cases
      .iter()
      .flat_map(|c| c.consequent.iter().copied())
      .collect(),
    StmtKind::Try {
      block,
      catch,
      finally_block,
    } => catch
      .iter()
      .map(|c| c.body)
      .chain(finally_block.iter().copied())
      .chain(std::iter::once(*block))
      .collect(),
    StmtKind::Labeled { body, .. } => vec![*body],
    StmtKind::With { body, .. } => vec![*body],
    _ => Vec::new(),
  }
}
