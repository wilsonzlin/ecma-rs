use crate::hir::Body;
use crate::hir::CatchBlock;
use crate::hir::ExprId;
use crate::hir::StmtId;
use crate::hir::StmtKind;

pub type BlockId = usize;

#[derive(Clone, Debug)]
pub struct BasicBlock {
  pub id: BlockId,
  pub stmts: Vec<StmtId>,
  pub terminator: Terminator,
}

#[derive(Clone, Debug)]
pub enum Terminator {
  End,
  Goto(BlockId),
  If {
    cond: ExprId,
    then_bb: BlockId,
    else_bb: BlockId,
  },
  Return,
}

#[derive(Clone, Debug)]
pub struct ControlFlowGraph {
  pub entry: BlockId,
  pub exit: BlockId,
  pub blocks: Vec<BasicBlock>,
}

struct Subgraph {
  entry: BlockId,
  exits: Vec<BlockId>,
}

pub fn build_cfg(body: &Body) -> ControlFlowGraph {
  let mut builder = CfgBuilder::new(body);
  let root = builder.build_stmt_list(&body.root);
  let exit = builder.new_block(Vec::new());
  for b in root.exits {
    builder.set_goto(b, exit);
  }
  ControlFlowGraph {
    entry: root.entry,
    exit,
    blocks: builder.blocks,
  }
}

struct CfgBuilder<'a> {
  body: &'a Body,
  blocks: Vec<BasicBlock>,
}

impl<'a> CfgBuilder<'a> {
  fn new(body: &'a Body) -> Self {
    Self {
      body,
      blocks: Vec::new(),
    }
  }

  fn new_block(&mut self, stmts: Vec<StmtId>) -> BlockId {
    let id = self.blocks.len();
    self.blocks.push(BasicBlock {
      id,
      stmts,
      terminator: Terminator::End,
    });
    id
  }

  fn set_goto(&mut self, from: BlockId, to: BlockId) {
    if matches!(self.blocks[from].terminator, Terminator::End) {
      self.blocks[from].terminator = Terminator::Goto(to);
    }
  }

  fn build_stmt_list(&mut self, stmts: &[StmtId]) -> Subgraph {
    if stmts.is_empty() {
      let block = self.new_block(Vec::new());
      return Subgraph {
        entry: block,
        exits: vec![block],
      };
    }

    let mut entry = None;
    let mut current_exits: Vec<BlockId> = Vec::new();
    for stmt_id in stmts.iter().copied() {
      let sg = self.build_stmt(stmt_id);
      if let Some(prev_exits) = if current_exits.is_empty() {
        None
      } else {
        Some(std::mem::take(&mut current_exits))
      } {
        for prev in prev_exits {
          self.set_goto(prev, sg.entry);
        }
      }
      if entry.is_none() {
        entry = Some(sg.entry);
      }
      current_exits.extend(sg.exits);
    }

    Subgraph {
      entry: entry.unwrap(),
      exits: current_exits,
    }
  }

  fn build_stmt(&mut self, stmt_id: StmtId) -> Subgraph {
    let stmt = &self.body.stmts[stmt_id.idx()];
    match &stmt.kind {
      StmtKind::Var { .. } | StmtKind::Expr(_) => {
        let block = self.new_block(vec![stmt_id]);
        Subgraph {
          entry: block,
          exits: vec![block],
        }
      }
      StmtKind::Return(_) => {
        let block = self.new_block(vec![stmt_id]);
        self.blocks[block].terminator = Terminator::Return;
        Subgraph {
          entry: block,
          exits: Vec::new(),
        }
      }
      StmtKind::Block(list) => self.build_stmt_list(list),
      StmtKind::If {
        cond,
        then_branch,
        else_branch,
      } => {
        let cond_block = self.new_block(Vec::new());
        let then_graph = self.build_stmt_list(then_branch);
        let else_graph = self.build_stmt_list(else_branch);
        self.blocks[cond_block].terminator = Terminator::If {
          cond: *cond,
          then_bb: then_graph.entry,
          else_bb: else_graph.entry,
        };
        Subgraph {
          entry: cond_block,
          exits: then_graph
            .exits
            .into_iter()
            .chain(else_graph.exits.into_iter())
            .collect(),
        }
      }
      StmtKind::While { cond, body } => {
        let cond_block = self.new_block(Vec::new());
        let body_graph = self.build_stmt_list(body);
        let exit_block = self.new_block(Vec::new());
        self.blocks[cond_block].terminator = Terminator::If {
          cond: *cond,
          then_bb: body_graph.entry,
          else_bb: exit_block,
        };
        for b in body_graph.exits {
          self.set_goto(b, cond_block);
        }
        Subgraph {
          entry: cond_block,
          exits: vec![exit_block],
        }
      }
      StmtKind::Try {
        try_block,
        catch,
        finally_block,
      } => self.build_try(try_block, catch.as_ref(), finally_block),
    }
  }

  fn build_try(
    &mut self,
    try_block: &[StmtId],
    catch: Option<&CatchBlock>,
    finally_block: &[StmtId],
  ) -> Subgraph {
    let try_graph = self.build_stmt_list(try_block);
    // Represent possible throw by connecting entry to catch as well.
    let catch_graph = if let Some(catch_block) = catch {
      self.build_stmt_list(&catch_block.body)
    } else {
      let empty = self.new_block(Vec::new());
      Subgraph {
        entry: empty,
        exits: vec![empty],
      }
    };

    let finally_graph = if finally_block.is_empty() {
      let empty = self.new_block(Vec::new());
      Subgraph {
        entry: empty,
        exits: vec![empty],
      }
    } else {
      self.build_stmt_list(finally_block)
    };

    let after = self.new_block(Vec::new());

    // Connect normal try exit and catch exit into finally/after.
    for exit in try_graph.exits {
      self.set_goto(exit, finally_graph.entry);
    }
    for exit in catch_graph.exits {
      self.set_goto(exit, finally_graph.entry);
    }
    for exit in finally_graph.exits.iter().copied() {
      self.set_goto(exit, after);
    }
    // Add edge to represent throw into catch.
    self.set_goto(try_graph.entry, catch_graph.entry);

    Subgraph {
      entry: try_graph.entry,
      exits: vec![after],
    }
  }
}
