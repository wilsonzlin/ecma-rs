//! Minimal control-flow graph representation for TypeScript bodies.
//!
//! The current checker builds a small, per-body CFG to drive flow-sensitive
//! analyses such as narrowing. The graph intentionally models only a subset of
//! statement kinds supported by the lightweight checker; it can be extended
//! incrementally as the checker gains new control-flow constructs.

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
  pub stmts: Vec<usize>,
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
    let entry = BlockId(0);
    let exit = BlockId(0);
    let block = BasicBlock {
      id: entry,
      stmts: Vec::new(),
      successors: Vec::new(),
    };
    ControlFlowGraph {
      entry,
      exit,
      blocks: vec![block],
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
      if !block.successors.contains(&to) {
        block.successors.push(to);
      }
    }
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
