use hir_js::{lower_from_source, Body, BodyKind, StmtId};
use std::sync::Arc;
use typecheck_ts::check::cfg::{BlockId, ControlFlowGraph};

fn cfg_for_first_function(source: &str) -> (ControlFlowGraph, Arc<Body>) {
  let lowered = lower_from_source(source).expect("lower source");
  let body = lowered
    .bodies
    .iter()
    .find(|b| matches!(b.kind, BodyKind::Function))
    .expect("function body")
    .clone();
  (ControlFlowGraph::from_body(body.as_ref()), body)
}

fn stmt_id_by_snippet(body: &Body, source: &str, snippet: &str) -> StmtId {
  let offset = source.find(snippet).expect("snippet should exist") as u32;
  body
    .stmts
    .iter()
    .enumerate()
    .find(|(_, stmt)| stmt.span.contains(offset))
    .map(|(idx, _)| StmtId(idx as u32))
    .expect("statement covering snippet")
}

fn block_for_stmt(cfg: &ControlFlowGraph, stmt: StmtId) -> BlockId {
  cfg
    .blocks
    .iter()
    .find(|block| block.stmts.contains(&stmt))
    .map(|block| block.id)
    .unwrap_or_else(|| panic!("block containing statement {:?}\n{cfg}", stmt))
}

fn update_block_for(cfg: &ControlFlowGraph, header: BlockId) -> BlockId {
  cfg
    .blocks
    .iter()
    .find(|block| {
      block.id != cfg.entry
        && block.stmts.is_empty()
        && matches!(
          block.kind,
          typecheck_ts::check::cfg::BlockKind::ForUpdate { .. }
        )
        && block.successors == [header]
    })
    .map(|block| block.id)
    .expect("update block")
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
fn break_in_switch_stays_in_loop_body() {
  let source = r#"
    function f(x: number) {
      while (true) {
        switch (x) {
          case 0:
            break;
          default:
            x = 1;
        }
        x = 2;
      }
    }
  "#;
  let (cfg, body) = cfg_for_first_function(source);
  let break_stmt = stmt_id_by_snippet(body.as_ref(), source, "break;");
  let after_switch_stmt = stmt_id_by_snippet(body.as_ref(), source, "x = 2;");
  let break_block = block_for_stmt(&cfg, break_stmt);
  let after_switch_block = block_for_stmt(&cfg, after_switch_stmt);

  assert!(
    reachable(&cfg, break_block, after_switch_block),
    "break inside switch should exit the switch but stay inside the loop body"
  );
}

#[test]
fn switch_cases_fall_through() {
  let source = r#"
    function f(x: number) {
      switch (x) {
        case 0:
          x = 1;
        case 1:
          x = 2;
      }
    }
  "#;
  let (cfg, body) = cfg_for_first_function(source);
  let first_case_stmt = stmt_id_by_snippet(body.as_ref(), source, "x = 1;");
  let second_case_stmt = stmt_id_by_snippet(body.as_ref(), source, "x = 2;");
  let first_block = block_for_stmt(&cfg, first_case_stmt);
  let second_block = block_for_stmt(&cfg, second_case_stmt);

  assert!(
    cfg.blocks[first_block.0]
      .successors
      .iter()
      .any(|succ| succ == &second_block),
    "first case should fall through into the second case"
  );
}

#[test]
fn continue_in_for_reaches_update() {
  let source = r#"
    function f() {
      for (let i = 0; i < 3; i++) {
        continue;
      }
    }
  "#;
  let (cfg, body) = cfg_for_first_function(source);
  let for_stmt = stmt_id_by_snippet(body.as_ref(), source, "for (let i");
  let continue_stmt = stmt_id_by_snippet(body.as_ref(), source, "continue;");

  let header_block = block_for_stmt(&cfg, for_stmt);
  let continue_block = block_for_stmt(&cfg, continue_stmt);
  let update_block = update_block_for(&cfg, header_block);

  assert_eq!(
    cfg.blocks[continue_block.0].successors,
    vec![update_block],
    "continue should jump to the update expression before re-evaluating the loop"
  );
  assert_eq!(
    cfg.blocks[update_block.0].successors,
    vec![header_block],
    "update should loop back to the header"
  );
}

#[test]
fn continue_in_switch_reaches_for_update() {
  let source = r#"
    function f() {
      for (let i = 0; i < 3; i++) {
        switch (i) {
          case 0:
            continue;
          default:
            i = 1;
        }
      }
    }
  "#;
  let (cfg, body) = cfg_for_first_function(source);
  let for_stmt = stmt_id_by_snippet(body.as_ref(), source, "for (let i");
  let continue_stmt = stmt_id_by_snippet(body.as_ref(), source, "continue;");

  let header_block = block_for_stmt(&cfg, for_stmt);
  let continue_block = block_for_stmt(&cfg, continue_stmt);
  let update_block = update_block_for(&cfg, header_block);

  assert_eq!(
    cfg.blocks[continue_block.0].successors,
    vec![update_block],
    "continue inside switch should still target the for-loop update before the next iteration"
  );
}

#[test]
fn labeled_break_targets_enclosing_label() {
  let source = r#"
    function f() {
      outer: while (true) {
        while (true) {
          break outer;
        }
      }
      const done = 1;
    }
  "#;
  let (cfg, body) = cfg_for_first_function(source);
  let break_stmt = stmt_id_by_snippet(body.as_ref(), source, "break outer;");
  let after_loop_stmt = stmt_id_by_snippet(body.as_ref(), source, "const done");
  let break_block = block_for_stmt(&cfg, break_stmt);
  let after_loop_block = block_for_stmt(&cfg, after_loop_stmt);

  assert!(
    reachable(&cfg, break_block, after_loop_block),
    "labeled break should exit the labeled loop"
  );
}

#[test]
fn labeled_continue_targets_labeled_loop() {
  let source = r#"
    function f() {
      outer: for (let i = 0; i < 3; i++) {
        while (true) {
          continue outer;
        }
      }
    }
  "#;
  let (cfg, body) = cfg_for_first_function(source);
  let continue_stmt = stmt_id_by_snippet(body.as_ref(), source, "continue outer;");
  let for_stmt = stmt_id_by_snippet(body.as_ref(), source, "for (let i");

  let header_block = block_for_stmt(&cfg, for_stmt);
  let update_block = update_block_for(&cfg, header_block);
  let continue_block = block_for_stmt(&cfg, continue_stmt);

  assert_eq!(
    cfg.blocks[continue_block.0].successors,
    vec![update_block],
    "labeled continue should target the labeled loop's continue point"
  );
}
