use ahash::{HashMap, HashSet};
use criterion::{criterion_group, criterion_main, Criterion};
use optimize_js::analysis::liveness::calculate_live_ins;
use optimize_js::cfg::cfg::{Cfg, CfgBBlocks, CfgGraph};
use optimize_js::il::inst::{Arg, Inst};
use std::hint::black_box;

fn build_block(label: u32, temps_per_block: u32) -> Vec<Inst> {
  (0..temps_per_block)
    .map(|offset| {
      let tgt = label * temps_per_block + offset;
      let src = tgt.saturating_sub(1);
      Inst::var_assign(tgt, Arg::Var(src))
    })
    .collect()
}

fn linear_cfg(blocks: u32, temps_per_block: u32) -> Cfg {
  let mut graph = CfgGraph::default();
  let mut bblocks = CfgBBlocks::default();
  for label in 0..blocks {
    if label + 1 < blocks {
      graph.connect(label, label + 1);
    }
    bblocks.add(label, build_block(label, temps_per_block));
  }
  Cfg {
    graph,
    bblocks,
    entry: 0,
  }
}

fn loop_cfg(blocks: u32, temps_per_block: u32) -> Cfg {
  let mut graph = CfgGraph::default();
  let mut bblocks = CfgBBlocks::default();
  let exit = blocks;
  bblocks.add(exit, Vec::new());
  for label in 0..blocks {
    let next = if label + 1 < blocks { label + 1 } else { 1 };
    graph.connect(label, next);
    if label % 5 == 0 {
      graph.connect(label, exit);
    }
    bblocks.add(label, build_block(label, temps_per_block));
  }
  Cfg {
    graph,
    bblocks,
    entry: 0,
  }
}

fn bench_liveness_linear(c: &mut Criterion) {
  let cfg = linear_cfg(200, 4);
  let inlines = HashMap::default();
  let inlined_vars = HashSet::default();
  c.bench_function("liveness linear 200 blocks", |b| {
    b.iter(|| calculate_live_ins(black_box(&cfg), &inlines, &inlined_vars))
  });
}

fn bench_liveness_loop(c: &mut Criterion) {
  let cfg = loop_cfg(120, 6);
  let inlines = HashMap::default();
  let inlined_vars = HashSet::default();
  c.bench_function("liveness loop with exits", |b| {
    b.iter(|| calculate_live_ins(black_box(&cfg), &inlines, &inlined_vars))
  });
}

criterion_group!(analysis, bench_liveness_linear, bench_liveness_loop);
criterion_main!(analysis);
