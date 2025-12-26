//! Minimal control-flow graph representation for TypeScript bodies built on top
//! of `hir-js`.
//!
//! The CFG deliberately operates at the statement level, producing one basic
//! block per [`StmtId`] and wiring edges for the common control-flow constructs
//! used by the lightweight checker (conditionals, switches, and loops).

use hir_js::{Body, StmtId, StmtKind};
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
  pub stmts: Vec<StmtId>,
  pub successors: Vec<BlockId>,
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
        "  {:?}: stmts={:?} succ={:?}",
        block.id, block.stmts, block.successors
      )?;
    }
    Ok(())
  }
}

/// Internal CFG builder that walks statement lists recursively.
struct CfgBuilder<'a> {
  cfg: ControlFlowGraph,
  body: &'a Body,
}

impl<'a> CfgBuilder<'a> {
  fn new(body: &'a Body) -> Self {
    let mut cfg = ControlFlowGraph::new();
    let entry = cfg.add_block();
    let exit = cfg.add_block();
    cfg.entry = entry;
    cfg.exit = exit;
    Self { cfg, body }
  }

  fn build(mut self) -> ControlFlowGraph {
    let mut referenced: HashSet<StmtId> = HashSet::new();
    for stmt in self.body.stmts.iter() {
      referenced.extend(child_stmt_ids(stmt));
    }

    let mut roots: Vec<StmtId> = (0..self.body.stmts.len() as u32)
      .map(StmtId)
      .filter(|id| !referenced.contains(id))
      .collect();
    roots.sort_by_key(|id| id.0);

    let entry_target = if roots.is_empty() {
      self.cfg.exit
    } else {
      self.build_stmt_list(&roots, self.cfg.exit)
    };
    self.cfg.add_edge(self.cfg.entry, entry_target);
    self.cfg
  }

  /// Build a linear chain of statements ending at `after`, returning the entry
  /// block for the first statement in the list (or `after` if empty).
  fn build_stmt_list(&mut self, stmts: &[StmtId], after: BlockId) -> BlockId {
    let mut next = after;
    for stmt in stmts.iter().rev() {
      next = self.build_stmt(*stmt, next);
    }
    next
  }

  /// Build a block for a single statement, connecting it to the continuation.
  fn build_stmt(&mut self, stmt_id: StmtId, after: BlockId) -> BlockId {
    let block = self.cfg.add_block();
    self.cfg.blocks[block.0].stmts.push(stmt_id);
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    match &stmt.kind {
      StmtKind::If {
        consequent,
        alternate,
        ..
      } => {
        let then_entry = self.build_stmt(*consequent, after);
        let else_entry = alternate
          .map(|alt| self.build_stmt(alt, after))
          .unwrap_or(after);
        self.cfg.add_edge(block, then_entry);
        self.cfg.add_edge(block, else_entry);
      }
      StmtKind::Switch { cases, .. } => {
        let mut has_default = false;
        for case in cases {
          if case.test.is_none() {
            has_default = true;
          }
          let entry = if case.consequent.is_empty() {
            after
          } else {
            self.build_stmt_list(&case.consequent, after)
          };
          self.cfg.add_edge(block, entry);
        }
        if !has_default {
          self.cfg.add_edge(block, after);
        }
      }
      StmtKind::While { body, .. } => {
        let body_entry = self.build_stmt(*body, block);
        self.cfg.add_edge(block, body_entry);
        self.cfg.add_edge(block, after);
      }
      StmtKind::DoWhile { body, .. } => {
        let body_entry = self.build_stmt(*body, block);
        self.cfg.add_edge(block, body_entry);
        self.cfg.add_edge(block, after);
      }
      StmtKind::For { body, .. } => {
        let body_entry = self.build_stmt(*body, block);
        self.cfg.add_edge(block, body_entry);
        self.cfg.add_edge(block, after);
      }
      StmtKind::ForIn { body, .. } => {
        let body_entry = self.build_stmt(*body, block);
        self.cfg.add_edge(block, body_entry);
        self.cfg.add_edge(block, after);
      }
      StmtKind::Block(stmts) => {
        let inner_entry = if stmts.is_empty() {
          after
        } else {
          self.build_stmt_list(stmts, after)
        };
        self.cfg.add_edge(block, inner_entry);
      }
      StmtKind::Try {
        block: inner,
        catch,
        finally_block,
      } => {
        let inner_entry = self.build_stmt(*inner, after);
        self.cfg.add_edge(block, inner_entry);
        if let Some(c) = catch {
          let catch_entry = self.build_stmt(c.body, after);
          self.cfg.add_edge(block, catch_entry);
        }
        if let Some(finally_stmt) = finally_block {
          let finally_entry = self.build_stmt(*finally_stmt, after);
          self.cfg.add_edge(block, finally_entry);
        }
      }
      StmtKind::Return(_) | StmtKind::Throw(_) => {
        // Return/throw terminates the current control flow; no outgoing edges.
      }
      _ => {
        self.cfg.add_edge(block, after);
      }
    }
    block
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
