use crate::analysis::find_conds::{find_conds, CondRegion};
use crate::analysis::find_loops::find_loops;
use crate::cfg::cfg::Cfg;
#[cfg(test)]
use crate::cfg::cfg::CfgBBlocks;
#[cfg(test)]
use crate::cfg::cfg::CfgGraph;
use crate::dom::{Dom, PostDom};
use crate::il::inst::{Arg, Const, Inst, InstTyp};
use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use itertools::Itertools;
use std::fmt;
use std::fmt::Write;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoopLabel(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BreakTarget {
  Loop(LoopLabel),
  Label(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
  Goto(u32),
  CondGoto { cond: Arg, t: u32, f: u32 },
  Stop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateBlock {
  pub label: u32,
  pub insts: Vec<Inst>,
  pub term: Terminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ControlTree {
  Seq(Vec<ControlTree>),
  Block {
    label: u32,
    insts: Vec<Inst>,
  },
  If {
    cond_block: u32,
    insts: Vec<Inst>,
    cond: Arg,
    then_t: Box<ControlTree>,
    else_t: Box<ControlTree>,
    join: u32,
  },
  Loop {
    header: u32,
    follow: Option<u32>,
    body: Box<ControlTree>,
    loop_label: LoopLabel,
  },
  Break {
    target: BreakTarget,
  },
  Continue {
    target: LoopLabel,
  },
  StateMachine {
    entry: u32,
    blocks: Vec<StateBlock>,
  },
}

impl ControlTree {
  pub fn to_debug_string(&self) -> String {
    let mut out = String::new();
    self.fmt_with_indent(0, &mut out).unwrap();
    out
  }

  fn fmt_with_indent(&self, indent: usize, out: &mut String) -> fmt::Result {
    let indent_str = "  ".repeat(indent);
    match self {
      ControlTree::Seq(nodes) => {
        writeln!(out, "{indent_str}Seq[")?;
        for n in nodes {
          n.fmt_with_indent(indent + 1, out)?;
        }
        writeln!(out, "{indent_str}]")
      }
      ControlTree::Block { label, insts } => {
        writeln!(out, "{indent_str}Block {label}:")?;
        for inst in insts {
          writeln!(out, "{}  {:?}", indent_str, inst)?;
        }
        Ok(())
      }
      ControlTree::If {
        cond_block,
        insts,
        cond,
        then_t,
        else_t,
        join,
      } => {
        writeln!(
          out,
          "{indent_str}If {cond_block} cond {:?} join {join}:",
          cond
        )?;
        if !insts.is_empty() {
          writeln!(out, "{indent_str}  cond_insts:")?;
          for inst in insts {
            writeln!(out, "{indent_str}    {:?}", inst)?;
          }
        }
        writeln!(out, "{indent_str}  then:")?;
        then_t.fmt_with_indent(indent + 2, out)?;
        writeln!(out, "{indent_str}  else:")?;
        else_t.fmt_with_indent(indent + 2, out)
      }
      ControlTree::Loop {
        header,
        follow,
        body,
        loop_label,
      } => {
        writeln!(
          out,
          "{indent_str}Loop {:?} header {header} follow {:?}:",
          loop_label, follow
        )?;
        body.fmt_with_indent(indent + 1, out)
      }
      ControlTree::Break { target } => writeln!(out, "{indent_str}Break {target:?}"),
      ControlTree::Continue { target } => writeln!(out, "{indent_str}Continue {:?}", target),
      ControlTree::StateMachine { entry, blocks } => {
        writeln!(out, "{indent_str}StateMachine entry {entry}:")?;
        for block in blocks {
          writeln!(out, "{indent_str}  state {}:", block.label)?;
          for inst in &block.insts {
            writeln!(out, "{indent_str}    {:?}", inst)?;
          }
          writeln!(out, "{indent_str}    term {:?}", block.term)?;
        }
        Ok(())
      }
    }
  }
}

fn wrap_seq(mut nodes: Vec<ControlTree>) -> ControlTree {
  if nodes.len() == 1 {
    nodes.pop().unwrap()
  } else {
    ControlTree::Seq(nodes)
  }
}

pub fn structure_cfg(cfg: &Cfg) -> ControlTree {
  let dom = Dom::calculate(cfg);
  let postdom = PostDom::calculate(cfg);
  let conds = find_conds(cfg, &dom, &postdom);
  let loops = LoopForest::new(cfg, &postdom, find_loops(cfg, &dom));
  let reachable = reachable_from_entry(cfg);
  let mut ctx = StructCtx {
    cfg,
    conds,
    loops,
    consumed: HashSet::new(),
    reachable,
  };

  if let Some(tree) = ctx.structure() {
    tree
  } else {
    build_state_machine(cfg)
  }
}

#[derive(Clone)]
struct LoopInfo {
  header: u32,
  nodes: HashSet<u32>,
  follow: Option<u32>,
  parent: Option<u32>,
  children: Vec<u32>,
}

struct LoopForest {
  loops: Vec<LoopInfo>,
  header_to_label: HashMap<u32, LoopLabel>,
  valid: bool,
}

impl LoopForest {
  fn new(cfg: &Cfg, postdom: &PostDom, raw: HashMap<u32, HashSet<u32>>) -> Self {
    let mut headers: Vec<_> = raw.keys().copied().collect();
    headers.sort_unstable();

    let mut loops = Vec::new();
    let mut header_to_label = HashMap::new();
    for (i, header) in headers.iter().enumerate() {
      let nodes = raw[header].clone();
      let follow = calculate_follow(cfg, postdom, &nodes);
      let label = LoopLabel(i);
      header_to_label.insert(*header, label);
      loops.push(LoopInfo {
        header: *header,
        nodes,
        follow,
        parent: None,
        children: Vec::new(),
      });
    }

    let mut valid = true;
    // Determine nesting relationships.
    for i in 0..loops.len() {
      let nodes_i = loops[i].nodes.clone();
      let mut parent: Option<(u32, usize)> = None;
      for j in 0..loops.len() {
        if i == j {
          continue;
        }
        let nodes_j = &loops[j].nodes;
        if nodes_i.len() < nodes_j.len() && nodes_i.is_subset(nodes_j) {
          let size = nodes_j.len();
          let replace = match parent {
            Some((parent_header, parent_size)) => {
              size < parent_size || (size == parent_size && loops[j].header < parent_header)
            }
            None => true,
          };
          if replace {
            parent = Some((loops[j].header, size));
          }
        } else if !nodes_j.is_subset(&nodes_i) && !nodes_i.is_disjoint(nodes_j) {
          // Overlapping but not nested.
          valid = false;
        }
      }
      loops[i].parent = parent.map(|(h, _)| h);
    }

    let mut child_edges = Vec::new();
    for idx in 0..loops.len() {
      if let Some(parent) = loops[idx].parent {
        if let Some(parent_idx) = header_to_label.get(&parent).map(|l| l.0) {
          child_edges.push((parent_idx, loops[idx].header));
        }
      }
    }
    for (parent_idx, child_header) in child_edges {
      loops[parent_idx].children.push(child_header);
    }

    for info in loops.iter_mut() {
      info.children.sort_unstable();
    }

    Self {
      loops,
      header_to_label,
      valid,
    }
  }

  fn is_valid(&self) -> bool {
    self.valid
  }

  fn label_for_header(&self, header: u32) -> Option<LoopLabel> {
    self.header_to_label.get(&header).copied()
  }

  fn info(&self, label: LoopLabel) -> &LoopInfo {
    &self.loops[label.0]
  }

  fn parent(&self, label: LoopLabel) -> Option<LoopLabel> {
    let header = self.info(label).parent?;
    self.label_for_header(header)
  }

  fn ancestor_containing(&self, mut label: LoopLabel, node: u32) -> Option<LoopLabel> {
    while let Some(parent) = self.parent(label) {
      if self.info(parent).nodes.contains(&node) {
        return Some(parent);
      }
      label = parent;
    }
    None
  }
}

fn calculate_follow(cfg: &Cfg, postdom: &PostDom, nodes: &HashSet<u32>) -> Option<u32> {
  let mut exits = Vec::new();
  for &n in nodes {
    for c in cfg.graph.children(n) {
      if !nodes.contains(&c) {
        exits.push(c);
      }
    }
  }
  exits.sort_unstable();
  exits.dedup();
  if exits.is_empty() {
    return None;
  }
  if exits.len() == 1 {
    return Some(exits[0]);
  }
  postdom.lca_all(exits.into_iter())
}

fn reachable_from_entry(cfg: &Cfg) -> HashSet<u32> {
  let mut seen = HashSet::new();
  let mut queue = vec![0];
  while let Some(n) = queue.pop() {
    if !seen.insert(n) {
      continue;
    }
    for c in cfg.graph.children(n) {
      queue.push(c);
    }
  }
  seen
}

struct StructCtx<'a> {
  cfg: &'a Cfg,
  conds: HashMap<u32, CondRegion>,
  loops: LoopForest,
  consumed: HashSet<u32>,
  reachable: HashSet<u32>,
}

struct NodeResult {
  nodes: Vec<ControlTree>,
  next: Option<u32>,
}

impl<'a> StructCtx<'a> {
  fn structure(&mut self) -> Option<ControlTree> {
    if !self.loops.is_valid() {
      return None;
    }
    let allowed = self.reachable.clone();
    let Ok(tree) = self.structure_seq(0, None, &allowed, None) else {
      return None;
    };
    if self.consumed == self.reachable {
      Some(tree)
    } else {
      None
    }
  }

  fn structure_seq(
    &mut self,
    start: u32,
    boundary: Option<u32>,
    allowed: &HashSet<u32>,
    current_loop: Option<LoopLabel>,
  ) -> Result<ControlTree, ()> {
    if let Some(boundary) = boundary {
      if start == boundary {
        return Ok(ControlTree::Seq(Vec::new()));
      }
    }
    let mut seq = Vec::new();
    let mut cursor = Some(start);
    while let Some(label) = cursor {
      if let Some(boundary) = boundary {
        if label == boundary {
          break;
        }
      }
      if let Some(current_loop) = current_loop {
        let loop_header = self.loops.info(current_loop).header;
        if label == loop_header && self.consumed.contains(&label) {
          seq.push(ControlTree::Continue {
            target: current_loop,
          });
          break;
        }
      }
      if !allowed.contains(&label) {
        return Err(());
      }
      if self.consumed.contains(&label) {
        return Err(());
      }

      if let Some(loop_label) = self.loops.label_for_header(label) {
        if self.loops.parent(loop_label) == current_loop {
          let info = self.loops.info(loop_label).clone();
          let res = self.structure_loop(loop_label, info)?;
          seq.extend(res.nodes);
          cursor = res.next;
          continue;
        }
      }

      if let Some(cond_region) = self.conds.get(&label).cloned() {
        let is_cond_goto = self
          .cfg
          .bblocks
          .maybe_get(label)
          .and_then(|block| block.last())
          .is_some_and(|inst| inst.t == InstTyp::CondGoto && inst.labels.len() == 2);
        if is_cond_goto {
          let res = self.structure_if(label, cond_region, allowed, current_loop)?;
          seq.extend(res.nodes);
          cursor = res.next;
          continue;
        }
      }

      let res = self.structure_block(label, allowed, current_loop)?;
      seq.extend(res.nodes);
      cursor = res.next;
    }
    Ok(wrap_seq(seq))
  }

  fn structure_block(
    &mut self,
    label: u32,
    allowed: &HashSet<u32>,
    current_loop: Option<LoopLabel>,
  ) -> Result<NodeResult, ()> {
    self.consumed.insert(label);
    let insts = self.cfg.bblocks.get(label).clone();
    let mut nodes = vec![ControlTree::Block { label, insts }];
    let mut children = self.cfg.graph.children(label).collect_vec();
    children.sort_unstable();
    match children.len() {
      0 => Ok(NodeResult { nodes, next: None }),
      1 => {
        let succ = children[0];
        match self.resolve_single_successor(current_loop, succ, allowed) {
          SuccessorResolution::Next(n) => Ok(NodeResult {
            nodes,
            next: Some(n),
          }),
          SuccessorResolution::Node(n) => {
            nodes.push(n);
            Ok(NodeResult { nodes, next: None })
          }
          SuccessorResolution::Err => Err(()),
        }
      }
      _ => Err(()),
    }
  }

  fn resolve_single_successor(
    &self,
    current_loop: Option<LoopLabel>,
    succ: u32,
    allowed: &HashSet<u32>,
  ) -> SuccessorResolution {
    if let Some(loop_label) = current_loop {
      let loop_info = self.loops.info(loop_label);
      if succ == loop_info.header {
        return SuccessorResolution::Node(ControlTree::Continue { target: loop_label });
      }
      if loop_info.follow == Some(succ) {
        return SuccessorResolution::Node(ControlTree::Break {
          target: BreakTarget::Loop(loop_label),
        });
      }
      if let Some(ancestor) = self.loops.ancestor_containing(loop_label, succ) {
        return SuccessorResolution::Node(ControlTree::Break {
          target: BreakTarget::Loop(ancestor),
        });
      }
    }

    if allowed.contains(&succ) {
      SuccessorResolution::Next(succ)
    } else {
      SuccessorResolution::Err
    }
  }

  fn structure_if(
    &mut self,
    label: u32,
    cond_region: CondRegion,
    allowed: &HashSet<u32>,
    current_loop: Option<LoopLabel>,
  ) -> Result<NodeResult, ()> {
    self.consumed.insert(label);
    let block = self.cfg.bblocks.get(label);
    let Some(last) = block.last() else {
      return Err(());
    };
    if last.t != InstTyp::CondGoto {
      return Err(());
    }
    let cond = last.args[0].clone();
    let insts = block[..block.len() - 1].to_vec();

    let then_tree = if cond_region.then_entry == cond_region.join {
      ControlTree::Seq(Vec::new())
    } else {
      self
        .structure_seq(
          cond_region.then_entry,
          Some(cond_region.join),
          allowed,
          current_loop,
        )
        .map_err(|_| ())?
    };
    let else_tree = if cond_region.else_entry == cond_region.join {
      ControlTree::Seq(Vec::new())
    } else {
      self
        .structure_seq(
          cond_region.else_entry,
          Some(cond_region.join),
          allowed,
          current_loop,
        )
        .map_err(|_| ())?
    };

    Ok(NodeResult {
      nodes: vec![ControlTree::If {
        cond_block: label,
        insts,
        cond,
        then_t: Box::new(then_tree),
        else_t: Box::new(else_tree),
        join: cond_region.join,
      }],
      next: Some(cond_region.join),
    })
  }

  fn structure_loop(&mut self, loop_label: LoopLabel, info: LoopInfo) -> Result<NodeResult, ()> {
    let guard = loop_guard(self.cfg, &info);
    if let Some(guard) = guard {
      self.consumed.insert(info.header);
      let then_tree = if guard.inside == info.header {
        ControlTree::Seq(Vec::new())
      } else {
        self
          .structure_seq(guard.inside, None, &info.nodes, Some(loop_label))
          .map_err(|_| ())?
      };
      let guard_if = ControlTree::If {
        cond_block: info.header,
        insts: guard.insts,
        cond: guard.cond,
        then_t: Box::new(then_tree),
        else_t: Box::new(ControlTree::Break {
          target: BreakTarget::Loop(loop_label),
        }),
        join: guard.outside,
      };
      let body = ControlTree::Seq(vec![guard_if]);
      let loop_node = ControlTree::Loop {
        header: info.header,
        follow: info.follow,
        body: Box::new(body),
        loop_label,
      };
      return Ok(NodeResult {
        nodes: vec![loop_node],
        next: info.follow,
      });
    }

    let body = self
      .structure_seq(info.header, None, &info.nodes, Some(loop_label))
      .map_err(|_| ())?;
    let loop_node = ControlTree::Loop {
      header: info.header,
      follow: info.follow,
      body: Box::new(body),
      loop_label,
    };
    Ok(NodeResult {
      nodes: vec![loop_node],
      next: info.follow,
    })
  }
}

enum SuccessorResolution {
  Next(u32),
  Node(ControlTree),
  Err,
}

struct GuardInfo {
  insts: Vec<Inst>,
  cond: Arg,
  inside: u32,
  outside: u32,
}

fn loop_guard(cfg: &Cfg, info: &LoopInfo) -> Option<GuardInfo> {
  let block = cfg.bblocks.get(info.header);
  let last = block.last()?;
  if last.t != InstTyp::CondGoto || last.labels.len() != 2 {
    return None;
  }
  let (inside, outside) =
    if info.nodes.contains(&last.labels[0]) && !info.nodes.contains(&last.labels[1]) {
      (last.labels[0], last.labels[1])
    } else if info.nodes.contains(&last.labels[1]) && !info.nodes.contains(&last.labels[0]) {
      (last.labels[1], last.labels[0])
    } else {
      return None;
    };
  if info.follow != Some(outside) {
    return None;
  }
  Some(GuardInfo {
    insts: block[..block.len() - 1].to_vec(),
    cond: last.args[0].clone(),
    inside,
    outside,
  })
}

fn build_state_machine(cfg: &Cfg) -> ControlTree {
  let mut labels: Vec<_> = cfg.graph.labels().collect();
  labels.sort_unstable();
  let mut blocks = Vec::new();
  for label in labels {
    let block = cfg.bblocks.get(label);
    let (insts, term) = build_terminator(block, cfg.graph.children(label));
    blocks.push(StateBlock { label, insts, term });
  }
  ControlTree::StateMachine { entry: 0, blocks }
}

fn build_terminator(
  block: &Vec<Inst>,
  children_iter: impl Iterator<Item = u32>,
) -> (Vec<Inst>, Terminator) {
  if let Some(last) = block.last() {
    if last.t == InstTyp::CondGoto {
      let insts = block[..block.len() - 1].to_vec();
      return (
        insts,
        Terminator::CondGoto {
          cond: last.args[0].clone(),
          t: last.labels[0],
          f: last.labels[1],
        },
      );
    }
  }
  let mut children = children_iter.collect_vec();
  children.sort_unstable();
  let term = match children.len() {
    0 => Terminator::Stop,
    1 => Terminator::Goto(children[0]),
    2 => Terminator::CondGoto {
      cond: Arg::Const(Const::Bool(true)),
      t: children[0],
      f: children[1],
    },
    _ => Terminator::Stop,
  };
  (block.clone(), term)
}

#[cfg(test)]
mod tests {
  use super::*;

  fn cfg_from_parts(blocks: &[(u32, Vec<Inst>)], edges: &[(u32, u32)]) -> Cfg {
    let mut graph = CfgGraph::default();
    for (p, c) in edges {
      graph.connect(*p, *c);
    }
    let mut bblocks = CfgBBlocks::default();
    for (label, insts) in blocks {
      bblocks.add(*label, insts.clone());
    }
    Cfg { graph, bblocks }
  }

  fn simple_inst(val: u32) -> Inst {
    Inst::var_assign(val, Arg::Const(Const::Bool(false)))
  }

  #[test]
  fn straight_line() {
    let cfg = cfg_from_parts(
      &[(0, vec![simple_inst(0)]), (1, vec![simple_inst(1)])],
      &[(0, 1)],
    );
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"Seq[
  Block 0:
    Inst { t: VarAssign, tgts: [0], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
  Block 1:
    Inst { t: VarAssign, tgts: [1], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
]
"#
    );
  }

  #[test]
  fn if_no_else() {
    let cfg = cfg_from_parts(
      &[
        (0, vec![Inst::cond_goto(Arg::Var(0), 1, 2)]),
        (1, vec![simple_inst(1)]),
        (2, vec![simple_inst(2)]),
      ],
      &[(0, 1), (0, 2), (1, 2)],
    );
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"Seq[
  If 0 cond %0 join 2:
    then:
      Block 1:
        Inst { t: VarAssign, tgts: [1], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
    else:
      Seq[
      ]
  Block 2:
    Inst { t: VarAssign, tgts: [2], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
]
"#
    );
  }

  #[test]
  fn if_else_diamond() {
    let cfg = cfg_from_parts(
      &[
        (0, vec![Inst::cond_goto(Arg::Var(0), 1, 2)]),
        (1, vec![simple_inst(1)]),
        (2, vec![simple_inst(2)]),
        (3, vec![simple_inst(3)]),
      ],
      &[(0, 1), (0, 2), (1, 3), (2, 3)],
    );
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"Seq[
  If 0 cond %0 join 3:
    then:
      Block 1:
        Inst { t: VarAssign, tgts: [1], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
    else:
      Block 2:
        Inst { t: VarAssign, tgts: [2], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
  Block 3:
    Inst { t: VarAssign, tgts: [3], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
]
"#
    );
  }

  #[test]
  fn while_with_guard() {
    let cfg = cfg_from_parts(
      &[
        (0, vec![Inst::cond_goto(Arg::Var(0), 1, 2)]),
        (1, vec![simple_inst(1)]),
        (2, vec![simple_inst(2)]),
      ],
      &[(0, 1), (0, 2), (1, 0)],
    );
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"Seq[
  Loop LoopLabel(0) header 0 follow Some(2):
    Seq[
      If 0 cond %0 join 2:
        then:
          Seq[
            Block 1:
              Inst { t: VarAssign, tgts: [1], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
            Continue LoopLabel(0)
          ]
        else:
          Break Loop(LoopLabel(0))
    ]
  Block 2:
    Inst { t: VarAssign, tgts: [2], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
]
"#
    );
  }

  #[test]
  fn nested_loops() {
    let cfg = cfg_from_parts(
      &[
        (0, vec![Inst::cond_goto(Arg::Var(0), 1, 4)]),
        (1, vec![simple_inst(1)]),
        (2, vec![Inst::cond_goto(Arg::Var(2), 3, 0)]),
        (3, vec![simple_inst(3)]),
        (4, vec![simple_inst(4)]),
      ],
      &[(0, 1), (0, 4), (1, 2), (2, 3), (2, 0), (3, 2)],
    );
    let tree = structure_cfg(&cfg);
    eprintln!("{}", tree.to_debug_string());
    assert_eq!(
      tree.to_debug_string(),
      r#"Seq[
  Loop LoopLabel(0) header 0 follow Some(4):
    Seq[
      If 0 cond %0 join 4:
        then:
          Seq[
            Block 1:
              Inst { t: VarAssign, tgts: [1], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
            Loop LoopLabel(1) header 2 follow Some(0):
              Seq[
                If 2 cond %2 join 0:
                  then:
                    Seq[
                      Block 3:
                        Inst { t: VarAssign, tgts: [3], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
                      Continue LoopLabel(1)
                    ]
                  else:
                    Break Loop(LoopLabel(1))
              ]
            Continue LoopLabel(0)
          ]
        else:
          Break Loop(LoopLabel(0))
    ]
  Block 4:
    Inst { t: VarAssign, tgts: [4], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
]
"#
    );
  }

  #[test]
  fn infinite_loop() {
    let cfg = cfg_from_parts(&[(0, vec![simple_inst(0)])], &[(0, 0)]);
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"Loop LoopLabel(0) header 0 follow None:
  Seq[
    Block 0:
      Inst { t: VarAssign, tgts: [0], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
    Continue LoopLabel(0)
  ]
"#
    );
  }

  #[test]
  fn short_circuit() {
    let cfg = cfg_from_parts(
      &[
        (0, vec![Inst::cond_goto(Arg::Var(0), 1, 3)]),
        (1, vec![Inst::cond_goto(Arg::Var(1), 2, 3)]),
        (2, vec![simple_inst(2)]),
        (3, vec![simple_inst(3)]),
      ],
      &[(0, 1), (0, 3), (1, 2), (1, 3), (2, 3)],
    );
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"Seq[
  If 0 cond %0 join 3:
    then:
      If 1 cond %1 join 3:
        then:
          Block 2:
            Inst { t: VarAssign, tgts: [2], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
        else:
          Seq[
          ]
    else:
      Seq[
      ]
  Block 3:
    Inst { t: VarAssign, tgts: [3], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
]
"#
    );
  }

  #[test]
  fn irreducible_fallback() {
    let cfg = cfg_from_parts(
      &[
        (0, vec![Inst::cond_goto(Arg::Var(0), 1, 2)]),
        (1, vec![simple_inst(1)]),
        (2, vec![simple_inst(2)]),
      ],
      &[(0, 1), (0, 2), (1, 2), (2, 1)],
    );
    let tree = structure_cfg(&cfg);
    assert_eq!(
      tree.to_debug_string(),
      r#"StateMachine entry 0:
  state 0:
    term CondGoto { cond: %0, t: 1, f: 2 }
  state 1:
    Inst { t: VarAssign, tgts: [1], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
    term Goto(2)
  state 2:
    Inst { t: VarAssign, tgts: [2], args: [false], spreads: [], labels: [], bin_op: _DUMMY, un_op: _DUMMY, foreign: SymbolId(4294967295), unknown: "" }
    term Goto(1)
"#
    );
  }
}
