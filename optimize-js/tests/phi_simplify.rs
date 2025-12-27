use optimize_js::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use optimize_js::il::inst::{Arg, Const, Inst, InstTyp};
use optimize_js::opt::optpass_cfg_prune::optpass_cfg_prune;
use optimize_js::opt::optpass_impossible_branches::optpass_impossible_branches;
use optimize_js::ssa::phi_simplify::{simplify_phis, validate_phis};
use parse_js::num::JsNumber;

#[test]
fn impossible_branches_prunes_phi_inputs() {
  let mut graph = CfgGraph::default();
  graph.connect(0, 1);
  graph.connect(0, 2);
  graph.connect(1, 3);
  graph.connect(2, 3);

  let mut bblocks = CfgBBlocks::default();
  bblocks.add(
    0,
    vec![Inst::cond_goto(Arg::Const(Const::Bool(true)), 1, 2)],
  );
  bblocks.add(
    1,
    vec![Inst::var_assign(10, Arg::Const(Const::Num(JsNumber(1.0))))],
  );
  bblocks.add(
    2,
    vec![Inst::var_assign(11, Arg::Const(Const::Num(JsNumber(2.0))))],
  );

  let mut phi = Inst::phi_empty(20);
  phi.insert_phi(1, Arg::Var(10));
  phi.insert_phi(2, Arg::Var(11));
  bblocks.add(3, vec![phi, Inst::var_assign(30, Arg::Var(20))]);

  let mut cfg = Cfg {
    graph,
    bblocks,
    entry: 0,
  };

  optpass_impossible_branches(&mut cfg);

  validate_phis(&cfg).unwrap();
  let block3 = cfg.bblocks.get(3);
  let (tgt, arg) = block3[0].as_var_assign();
  assert_eq!(tgt, 20);
  assert_eq!(*arg, Arg::Var(10));
}

#[test]
fn cfg_prune_converts_redundant_phi_to_assign() {
  let mut graph = CfgGraph::default();
  graph.connect(0, 1);
  graph.connect(0, 2);
  graph.connect(1, 2);
  graph.connect(3, 2);

  let mut bblocks = CfgBBlocks::default();
  bblocks.add(
    0,
    vec![Inst::var_assign(0, Arg::Const(Const::Num(JsNumber(0.0))))],
  );
  bblocks.add(1, vec![]);
  bblocks.add(
    3,
    vec![Inst::var_assign(50, Arg::Const(Const::Num(JsNumber(3.0))))],
  );

  let mut phi = Inst::phi_empty(5);
  phi.insert_phi(1, Arg::Const(Const::Num(JsNumber(1.0))));
  phi.insert_phi(0, Arg::Const(Const::Num(JsNumber(0.0))));
  bblocks.add(2, vec![phi]);

  let mut cfg = Cfg {
    graph,
    bblocks,
    entry: 0,
  };

  optpass_cfg_prune(&mut cfg);

  validate_phis(&cfg).unwrap();
  let mut assignments = Vec::new();
  for (_, block) in cfg.bblocks.all() {
    for inst in block {
      assert_ne!(inst.t, InstTyp::Phi);
      if inst.t == InstTyp::VarAssign && inst.tgts[0] == 5 {
        assignments.push(inst.args[0].clone());
      }
    }
  }
  assert_eq!(assignments, vec![Arg::Const(Const::Num(JsNumber(1.0)))]);
}

#[test]
fn empty_phi_is_replaced_with_defined_value_when_used() {
  let mut graph = CfgGraph::default();
  graph.connect(0, 1);

  let mut bblocks = CfgBBlocks::default();
  bblocks.add(0, vec![]);
  bblocks.add(
    1,
    vec![
      Inst::phi_empty(7),
      Inst::var_assign(8, Arg::Var(7)),
      Inst::var_assign(9, Arg::Const(Const::Num(JsNumber(3.0)))),
    ],
  );

  let mut cfg = Cfg {
    graph,
    bblocks,
    entry: 0,
  };

  assert!(simplify_phis(&mut cfg));
  validate_phis(&cfg).unwrap();
  let block1 = cfg.bblocks.get(1);
  assert_eq!(block1[0].t, InstTyp::VarAssign);
  let (tgt, arg) = block1[0].as_var_assign();
  assert_eq!(tgt, 7);
  assert_eq!(*arg, Arg::Const(Const::Undefined));
  let (_, use_arg) = block1[1].as_var_assign();
  assert_eq!(*use_arg, Arg::Var(7));
}
