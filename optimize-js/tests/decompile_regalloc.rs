use optimize_js::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use optimize_js::decompile::regalloc::compute_regalloc;
use optimize_js::il::inst::{Arg, Const, Inst};

fn build_cfg(blocks: Vec<(u32, Vec<Inst>)>, edges: &[(u32, u32)]) -> Cfg {
  let mut graph = CfgGraph::default();
  // Ensure every label exists in the graph for liveness, even if it has no edges.
  for (label, _) in blocks.iter() {
    graph.connect(*label, *label);
    graph.disconnect(*label, *label);
  }
  for &(parent, child) in edges {
    graph.connect(parent, child);
  }
  let mut bblocks = CfgBBlocks::default();
  for (label, insts) in blocks {
    bblocks.add(label, insts);
  }
  Cfg {
    graph,
    bblocks,
    entry: 0,
  }
}

#[test]
fn straight_line_registers_do_not_exceed_temps() {
  let insts = vec![
    Inst::var_assign(0, Arg::Const(Const::Bool(true))),
    // temp 0 is used twice so it should not be inlined.
    Inst::var_assign(1, Arg::Var(0)),
    Inst::var_assign(2, Arg::Var(0)),
    Inst::prop_assign(
      Arg::Var(1),
      Arg::Const(Const::Str("a".into())),
      Arg::Const(Const::Bool(false)),
    ),
    Inst::prop_assign(
      Arg::Var(2),
      Arg::Const(Const::Str("b".into())),
      Arg::Const(Const::Bool(true)),
    ),
  ];
  let cfg = build_cfg(vec![(0, insts)], &[]);
  let regalloc = compute_regalloc(&cfg);

  let temp_count = 3;
  assert!(
    regalloc.reg_count <= temp_count,
    "allocated {:#?}",
    regalloc
  );
  assert!(regalloc
    .temp_to_reg
    .values()
    .all(|r| *r < regalloc.reg_count));
  assert!(
    regalloc.inlined_temps.contains(&1) && regalloc.inlined_temps.contains(&2),
    "single-use temps should be inlined where possible"
  );
  assert!(
    !regalloc.inlined_temps.contains(&0),
    "multi-use temps should not be inlined"
  );
}

#[test]
fn non_overlapping_temps_reuse_registers() {
  // 0 -> 1 -> 2 -> 3 -> 4
  // Each temp is defined in one block and used in the next, so live ranges do not overlap.
  let cfg = build_cfg(
    vec![
      (0, vec![Inst::var_assign(0, Arg::Const(Const::Bool(true)))]),
      (1, vec![Inst::var_assign(1, Arg::Var(0))]),
      (
        2,
        vec![Inst::prop_assign(
          Arg::Var(1),
          Arg::Const(Const::Str("x".into())),
          Arg::Const(Const::Bool(true)),
        )],
      ),
      (3, vec![Inst::var_assign(2, Arg::Const(Const::Bool(false)))]),
      (
        4,
        vec![Inst::prop_assign(
          Arg::Var(2),
          Arg::Const(Const::Str("y".into())),
          Arg::Const(Const::Bool(false)),
        )],
      ),
    ],
    &[(0, 1), (1, 2), (2, 3), (3, 4)],
  );

  let regalloc = compute_regalloc(&cfg);

  assert_eq!(
    regalloc.reg_count, 1,
    "live ranges should pack into one reg"
  );
  assert_eq!(
    regalloc.temp_to_reg[&1], regalloc.temp_to_reg[&2],
    "non-overlapping temps should reuse registers"
  );
}

#[test]
fn loop_carried_values_are_not_inlined_into_phi() {
  // The Phi at the top of the loop consumes a value defined later in the block to carry the
  // updated loop variable across iterations. That value must not be considered single-use.
  let mut phi = Inst::phi_empty(0);
  phi.insert_phi(0, Arg::Const(Const::Bool(false)));
  phi.insert_phi(1, Arg::Var(2));

  let loop_block = vec![
    phi,
    Inst::var_assign(1, Arg::Var(0)),
    // Self-assignment through the Phi.
    Inst::var_assign(2, Arg::Var(0)),
  ];
  let cfg = build_cfg(vec![(0, vec![]), (1, loop_block)], &[(0, 1), (1, 1)]);

  let regalloc = compute_regalloc(&cfg);

  assert!(
    !regalloc.inlined_temps.contains(&2),
    "loop-carried defs used by Phi must not be inlined"
  );
  assert!(
    !regalloc.inlines.contains_key(&(1, 2)),
    "inline plan should not inline the loop-carried inst"
  );
}
