use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use optimize_js::{compile_source, Program, TopLevelMode};
use std::hint::black_box;

fn dom_calculations(program: &Program) -> usize {
  program.top_level.stats.dom_calculations
    + program
      .functions
      .iter()
      .map(|func| func.stats.dom_calculations)
      .sum::<usize>()
}

fn bench_dom_recomputation(c: &mut Criterion) {
  let sources: &[(&str, &str)] = &[
    (
      "instruction_only_iterations",
      r#"
        let x = 1 + 2;
        let y = x + 0;
        x + y;
      "#,
    ),
    (
      "cfg_change_from_const_branch",
      r#"
        if (false) {
          let never = 1;
        } else {
          let taken = 2;
          taken;
        }
      "#,
    ),
    (
      "megatest_optimizable_0",
      include_str!("../../megatest/optimizable_0.js"),
    ),
  ];

  let mut group = c.benchmark_group("dom_recomputations");
  for (name, source) in sources {
    let baseline = compile_source(source, TopLevelMode::Module, false).expect("compile baseline");
    let expected_dom = dom_calculations(&baseline) as u64;
    group.throughput(Throughput::Elements(expected_dom));
    group.bench_function(BenchmarkId::new("compile", name), |b| {
      b.iter(|| {
        let program =
          compile_source(black_box(*source), TopLevelMode::Module, false).expect("compile");
        let doms = dom_calculations(&program) as u64;
        assert_eq!(
          doms, expected_dom,
          "dom calculations should be deterministic"
        );
        black_box(doms);
      });
    });
  }
  group.finish();
}

criterion_group!(optimization, bench_dom_recomputation);
criterion_main!(optimization);
