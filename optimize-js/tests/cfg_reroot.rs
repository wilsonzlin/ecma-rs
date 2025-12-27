use optimize_js::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use optimize_js::dom::Dom;
use optimize_js::il::inst::{Arg, Const, Inst};
use optimize_js::opt::optpass_cfg_prune::optpass_cfg_prune;
use optimize_js::ssa::ssa_rename::rename_targets_for_ssa_construction;
use optimize_js::util::counter::Counter;

fn simple_cfg_with_entry_jump() -> Cfg {
  let mut graph = CfgGraph::default();
  graph.connect(0, 1);
  graph.connect(1, 2);
  graph.connect(1, 3);

  let mut bblocks = CfgBBlocks::default();
  bblocks.add(0, vec![]);
  bblocks.add(
    1,
    vec![
      Inst::var_assign(0, Arg::Const(Const::Bool(true))),
      Inst::cond_goto(Arg::Var(0), 2, 3),
    ],
  );
  bblocks.add(2, vec![Inst::var_assign(1, Arg::Var(0))]);
  bblocks.add(3, vec![Inst::var_assign(2, Arg::Var(0))]);

  Cfg {
    graph,
    bblocks,
    entry: 0,
  }
}

#[test]
fn reroots_empty_entry_block() {
  let mut cfg = simple_cfg_with_entry_jump();

  let result = optpass_cfg_prune(&mut cfg);

  assert!(result.changed, "pruning should reroot the cfg");
  assert_eq!(cfg.entry, 1, "entry should move to the only child");
  assert!(
    !cfg.graph.contains(0) && cfg.bblocks.maybe_get(0).is_none(),
    "old entry block should be removed entirely"
  );
  assert!(
    cfg.graph.parents_sorted(1).is_empty(),
    "new entry should not have predecessors after rerooting"
  );
  assert_eq!(
    cfg.graph.children_sorted(cfg.entry),
    vec![2, 3],
    "existing edges should be preserved from the new root"
  );
}

#[test]
fn dominance_and_ssa_handle_new_entry() {
  let mut cfg = simple_cfg_with_entry_jump();

  optpass_cfg_prune(&mut cfg);
  let dom = Dom::calculate(&cfg);
  assert_eq!(dom.entry_label(), cfg.entry);
  assert_eq!(dom.idom_of(2), Some(1));

  let mut counter = Counter::new(10);
  rename_targets_for_ssa_construction(&mut cfg, &dom, &mut counter);

  let entry_block = cfg.bblocks.get(cfg.entry);
  assert_eq!(entry_block[0].tgts, vec![10]);
  assert_eq!(entry_block[1].args, vec![Arg::Var(10)]);

  let child_block = cfg.bblocks.get(2);
  assert_eq!(child_block[0].tgts, vec![11]);
  assert_eq!(child_block[0].args, vec![Arg::Var(10)]);

  let other_child = cfg.bblocks.get(3);
  assert_eq!(other_child[0].tgts, vec![12]);
  assert_eq!(other_child[0].args, vec![Arg::Var(10)]);
}
