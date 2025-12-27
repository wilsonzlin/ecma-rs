use optimize_js::analysis::defs::calculate_defs;
use optimize_js::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use optimize_js::dom::Dom;
use optimize_js::il::inst::{Arg, Const, Inst, InstTyp};
use optimize_js::ssa::ssa_insert_phis::insert_phis_for_ssa_construction;
use optimize_js::ssa::ssa_rename::rename_targets_for_ssa_construction;
use optimize_js::util::counter::Counter;

#[test]
fn phi_inputs_are_added_when_definition_is_missing_on_a_path() {
  let mut graph = CfgGraph::default();
  graph.connect(0, 1);
  graph.connect(0, 2);
  graph.connect(1, 3);
  graph.connect(2, 3);

  let mut bblocks = CfgBBlocks::default();
  bblocks.add(0, vec![Inst::cond_goto(Arg::Var(0), 1, 2)]);
  bblocks.add(1, vec![Inst::var_assign(1, Arg::Const(Const::Bool(true)))]);
  bblocks.add(2, vec![]);
  bblocks.add(3, vec![Inst::var_assign(2, Arg::Var(1))]);

  let mut cfg = Cfg { graph, bblocks };

  let mut defs = calculate_defs(&cfg);
  let dom = Dom::calculate(&cfg);
  insert_phis_for_ssa_construction(&mut defs, &mut cfg, &dom);
  let mut c_temp = Counter::new(3);
  rename_targets_for_ssa_construction(&mut cfg, &dom, &mut c_temp);

  let join = cfg.bblocks.get(3);
  assert!(matches!(join.first(), Some(inst) if inst.t == InstTyp::Phi));
  let phi = &join[0];
  assert_eq!(phi.labels.len(), 2);
  let mut labels = phi.labels.clone();
  labels.sort_unstable();
  assert_eq!(labels, vec![1, 2]);
  let else_arg = phi
    .labels
    .iter()
    .zip(phi.args.iter())
    .find(|(l, _)| **l == 2)
    .map(|(_, arg)| arg)
    .unwrap();
  assert_eq!(else_arg, &Arg::Var(1));
}

#[test]
fn trivial_phi_is_pruned_and_uses_are_rewritten() {
  let mut graph = CfgGraph::default();
  graph.connect(0, 1);

  let mut bblocks = CfgBBlocks::default();
  bblocks.add(0, vec![Inst::var_assign(1, Arg::Const(Const::Bool(true)))]);
  bblocks.add(
    1,
    vec![Inst::phi_empty(1), Inst::var_assign(2, Arg::Var(1))],
  );

  let mut cfg = Cfg { graph, bblocks };

  let mut defs = calculate_defs(&cfg);
  let dom = Dom::calculate(&cfg);
  insert_phis_for_ssa_construction(&mut defs, &mut cfg, &dom);
  let mut c_temp = Counter::new(3);
  rename_targets_for_ssa_construction(&mut cfg, &dom, &mut c_temp);

  let block1 = cfg.bblocks.get(1);
  assert!(!matches!(block1.first(), Some(inst) if inst.t == InstTyp::Phi));

  let (def_tgt, _) = cfg.bblocks.get(0)[0].as_var_assign();
  let (_, arg) = cfg.bblocks.get(1)[0].as_var_assign();
  assert_eq!(arg, &Arg::Var(def_tgt));
}
