use criterion::black_box;
use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use parse_js::ast::node::NodeAssocData;

fn bench_node_assoc_data(c: &mut Criterion) {
  c.bench_function("set_single", |b| {
    b.iter(|| {
      let mut assoc = NodeAssocData::default();
      assoc.set(black_box(1u32));
      black_box(assoc);
    })
  });

  c.bench_function("overwrite_single", |b| {
    let mut assoc = NodeAssocData::default();
    assoc.set(1u32);
    b.iter(|| assoc.set(black_box(2u32)))
  });

  c.bench_function("get_two_types", |b| {
    let mut assoc = NodeAssocData::default();
    assoc.set(1u32);
    assoc.set("hello");
    b.iter(|| {
      black_box(assoc.get::<u32>().unwrap());
      black_box(assoc.get::<&'static str>().unwrap());
    })
  });

  c.bench_function("remove_single", |b| {
    b.iter(|| {
      let mut assoc = NodeAssocData::default();
      assoc.set(black_box(1u32));
      black_box(assoc.remove::<u32>());
    })
  });
}

criterion_group!(benches, bench_node_assoc_data);
criterion_main!(benches);
