use hir_js::{lower_from_source, Body};
use typecheck_ts::check::cfg::{BlockId, BlockKind, ControlFlowGraph};

fn root_body(lowered: &hir_js::LowerResult) -> &Body {
  let body_id = lowered.root_body();
  lowered.body(body_id).expect("root body")
}

fn reachable(cfg: &ControlFlowGraph, from: BlockId, to: BlockId) -> bool {
  let mut stack = vec![from];
  let mut visited = std::collections::HashSet::new();
  while let Some(block) = stack.pop() {
    if !visited.insert(block) {
      continue;
    }
    if block == to {
      return true;
    }
    if let Some(node) = cfg.blocks.get(block.0) {
      stack.extend(node.successors.iter().copied());
    }
  }
  false
}

#[test]
fn for_loop_uses_distinct_blocks() {
  let lowered = lower_from_source("for (let i = 0; i < 3; i++) i;").expect("lower");
  let cfg = ControlFlowGraph::from_body(root_body(&lowered));

  let init = cfg
    .blocks
    .iter()
    .find(|b| matches!(b.kind, BlockKind::ForInit { .. }))
    .expect("init block")
    .id;
  let test = cfg
    .blocks
    .iter()
    .find(|b| matches!(b.kind, BlockKind::ForTest { .. }))
    .expect("test block")
    .id;
  let update = cfg
    .blocks
    .iter()
    .find(|b| matches!(b.kind, BlockKind::ForUpdate { .. }))
    .expect("update block")
    .id;

  assert_eq!(cfg.blocks[cfg.entry.0].successors, vec![init]);
  assert_eq!(cfg.blocks[init.0].successors, vec![test]);

  assert_eq!(
    cfg.blocks[test.0].successors.len(),
    2,
    "for-test should have two outgoing edges"
  );

  let body_entry = cfg.blocks[test.0]
    .successors
    .iter()
    .copied()
    .find(|succ| reachable(&cfg, *succ, update))
    .expect("body edge");
  let after = cfg.blocks[test.0]
    .successors
    .iter()
    .copied()
    .find(|succ| *succ != body_entry)
    .expect("after edge");
  assert!(
    reachable(&cfg, body_entry, update),
    "body should reach update"
  );
  assert!(
    reachable(&cfg, after, cfg.exit),
    "false edge should reach cfg exit"
  );
  assert_eq!(cfg.blocks[update.0].successors, vec![test]);
}

#[test]
fn do_while_executes_body_before_test() {
  let lowered = lower_from_source("do x; while (x);").expect("lower");
  let cfg = ControlFlowGraph::from_body(root_body(&lowered));

  let test_block = cfg
    .blocks
    .iter()
    .find(|b| matches!(b.kind, BlockKind::DoWhileTest { .. }))
    .expect("test block")
    .id;

  let entry_succ = *cfg
    .blocks
    .get(cfg.entry.0)
    .and_then(|b| b.successors.first())
    .expect("entry successor");

  assert_ne!(entry_succ, test_block, "should enter body before testing");
  assert!(
    cfg.blocks[entry_succ.0].successors.contains(&test_block),
    "body should flow to test"
  );
  assert!(
    cfg.blocks[test_block.0].successors.contains(&entry_succ),
    "test true edge should loop"
  );
  let after = cfg.blocks[test_block.0]
    .successors
    .iter()
    .copied()
    .find(|succ| *succ != entry_succ)
    .expect("after edge");
  assert!(
    reachable(&cfg, after, cfg.exit),
    "test false edge should reach cfg exit"
  );
}
