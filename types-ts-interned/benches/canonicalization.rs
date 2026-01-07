use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use ordered_float::OrderedFloat;
use std::hint::black_box;
use types_ts_interned::{TypeId, TypeKind, TypeStore};

fn intern_string_literals(store: &TypeStore, prefix: &str, count: usize) -> Vec<TypeId> {
  (0..count)
    .map(|idx| {
      let name = store.intern_name(format!("{prefix}{idx:04}"));
      store.intern_type(TypeKind::StringLiteral(name))
    })
    .collect()
}

fn intern_number_literals(store: &TypeStore, count: usize) -> Vec<TypeId> {
  (0..count)
    .map(|idx| store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(idx as f64))))
    .collect()
}

fn bench_canonicalization(c: &mut Criterion) {
  let store = TypeStore::new();
  let mut group = c.benchmark_group("types-ts-interned/canonicalization");

  let flat = intern_string_literals(&store, "u", 1024);
  let flat_dupes: Vec<_> = flat.iter().copied().chain(flat.iter().copied()).collect();
  group.bench_function("union/flat_2048_dupes", |b| {
    b.iter_batched(
      || flat_dupes.clone(),
      |members| black_box(store.union(members)),
      BatchSize::LargeInput,
    );
  });

  let nested_literals = intern_string_literals(&store, "n", 2048);
  let nested_unions: Vec<_> = nested_literals
    .chunks(8)
    .map(|chunk| store.intern_type(TypeKind::Union(chunk.to_vec())))
    .collect();
  group.bench_function("union/nested_256x8", |b| {
    b.iter_batched(
      || nested_unions.clone(),
      |members| black_box(store.union(members)),
      BatchSize::LargeInput,
    );
  });

  let nums = intern_number_literals(&store, 1024);
  let nums_dupes: Vec<_> = nums.iter().copied().chain(nums.iter().copied()).collect();
  group.bench_function("intersection/flat_2048_dupes", |b| {
    b.iter_batched(
      || nums_dupes.clone(),
      |members| black_box(store.intersection(members)),
      BatchSize::LargeInput,
    );
  });

  let nested_nums = intern_number_literals(&store, 2048);
  let nested_intersections: Vec<_> = nested_nums
    .chunks(8)
    .map(|chunk| store.intern_type(TypeKind::Intersection(chunk.to_vec())))
    .collect();
  group.bench_function("intersection/nested_256x8", |b| {
    b.iter_batched(
      || nested_intersections.clone(),
      |members| black_box(store.intersection(members)),
      BatchSize::LargeInput,
    );
  });

  group.finish();
}

criterion_group!(benches, bench_canonicalization);
criterion_main!(benches);
