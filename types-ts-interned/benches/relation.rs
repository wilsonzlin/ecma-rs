use criterion::{criterion_group, criterion_main, BatchSize, Criterion, Throughput};
use std::hint::black_box;
use types_ts_interned::{
  CacheConfig, CacheStats, EvaluatorCacheStats, EvaluatorCaches, Indexer, Param, PropData, PropKey,
  Property, RelationCache, RelateCtx, RelateHooks, Shape, Signature, TypeId, TypeKind, TypeStore,
};

fn hit_rate(stats: CacheStats) -> f64 {
  let total = stats.hits + stats.misses;
  if total == 0 {
    0.0
  } else {
    stats.hits as f64 / total as f64
  }
}

fn delta_stats(after: CacheStats, before: CacheStats) -> CacheStats {
  CacheStats {
    hits: after.hits.saturating_sub(before.hits),
    misses: after.misses.saturating_sub(before.misses),
    insertions: after.insertions.saturating_sub(before.insertions),
    evictions: after.evictions.saturating_sub(before.evictions),
  }
}

fn delta_evaluator_stats(after: EvaluatorCacheStats, before: EvaluatorCacheStats) -> EvaluatorCacheStats {
  EvaluatorCacheStats {
    eval: delta_stats(after.eval, before.eval),
    references: delta_stats(after.references, before.references),
  }
}

fn print_cache_stats(label: &str, stats: CacheStats) {
  println!(
    "{label}: hits={} misses={} hit_rate={:.3} insertions={} evictions={}",
    stats.hits,
    stats.misses,
    hit_rate(stats),
    stats.insertions,
    stats.evictions
  );
}

fn print_evaluator_stats(label: &str, stats: EvaluatorCacheStats) {
  println!("{label}:");
  print_cache_stats("  eval", stats.eval);
  print_cache_stats("  refs", stats.references);
}

fn new_ctx(store: std::sync::Arc<TypeStore>, config: CacheConfig) -> RelateCtx<'static> {
  let hooks: RelateHooks<'static> = RelateHooks::default();
  RelateCtx::with_hooks_cache_and_normalizer_caches(
    store.clone(),
    store.options(),
    hooks,
    RelationCache::new(config),
    EvaluatorCaches::new(config),
  )
}

fn intern_string_literals(store: &TypeStore, prefix: &str, count: usize) -> Vec<TypeId> {
  (0..count)
    .map(|idx| {
      let name = store.intern_name(format!("{prefix}{idx:04}"));
      store.intern_type(TypeKind::StringLiteral(name))
    })
    .collect()
}

fn build_object_pair(store: &TypeStore, base_props: usize, extra_props: usize) -> (TypeId, TypeId) {
  let prim = store.primitive_ids();
  let mut shape = Shape::new();

  let string_or_number = store.union(vec![prim.string, prim.number]);
  let bool_or_number = store.union(vec![prim.boolean, prim.number]);

  for idx in 0..base_props {
    let name = store.intern_name(format!("p{idx:04}"));
    let ty = match idx % 4 {
      0 => prim.string,
      1 => prim.number,
      2 => string_or_number,
      _ => bool_or_number,
    };
    shape.properties.push(Property {
      key: PropKey::String(name),
      data: PropData {
        ty,
        optional: idx % 6 == 0,
        readonly: idx % 9 == 0,
        accessibility: None,
        is_method: idx % 7 == 0,
        origin: None,
        declared_on: None,
      },
    });
  }

  for idx in 0..8 {
    let sig = store.intern_signature(Signature::new(
      vec![
        Param {
          name: None,
          ty: if idx % 2 == 0 { string_or_number } else { prim.string },
          optional: idx % 3 == 0,
          rest: false,
        },
        Param {
          name: None,
          ty: if idx % 2 == 0 { prim.number } else { bool_or_number },
          optional: idx % 4 == 0,
          rest: idx % 5 == 0,
        },
      ],
      if idx % 2 == 0 { prim.boolean } else { prim.number },
    ));
    shape.call_signatures.push(sig);
  }

  for idx in 0..4 {
    let sig = store.intern_signature(Signature::new(
      vec![Param {
        name: None,
        ty: if idx % 2 == 0 { prim.number } else { prim.string },
        optional: false,
        rest: idx % 2 == 0,
      }],
      prim.any,
    ));
    shape.construct_signatures.push(sig);
  }

  shape.indexers.push(Indexer {
    key_type: prim.string,
    value_type: string_or_number,
    readonly: false,
  });
  shape.indexers.push(Indexer {
    key_type: prim.number,
    value_type: bool_or_number,
    readonly: true,
  });

  let dst_shape = store.intern_shape(shape.clone());
  let dst_obj = store.intern_object(types_ts_interned::ObjectType { shape: dst_shape });
  let dst_ty = store.intern_type(TypeKind::Object(dst_obj));

  // Source type has additional properties; destination keys are a subset, so assignability should
  // still traverse the full destination shape (properties + indexers + signatures).
  for idx in 0..extra_props {
    let name = store.intern_name(format!("extra{idx:04}"));
    shape.properties.push(Property {
      key: PropKey::String(name),
      data: PropData {
        ty: string_or_number,
        optional: true,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }

  let src_shape = store.intern_shape(shape);
  let src_obj = store.intern_object(types_ts_interned::ObjectType { shape: src_shape });
  let src_ty = store.intern_type(TypeKind::Object(src_obj));

  (src_ty, dst_ty)
}

fn build_deep_object_chain(store: &TypeStore, depth: usize, extra_props: bool) -> TypeId {
  let prim = store.primitive_ids();

  let value_name = store.intern_name("value");
  let mut leaf = Shape::new();
  leaf.properties.push(Property {
    key: PropKey::String(value_name),
    data: PropData {
      ty: prim.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  if extra_props {
    leaf.properties.push(Property {
      key: PropKey::String(store.intern_name("extra_leaf")),
      data: PropData {
        ty: prim.string,
        optional: true,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }
  let leaf_shape = store.intern_shape(leaf);
  let leaf_obj = store.intern_object(types_ts_interned::ObjectType { shape: leaf_shape });
  let mut current = store.intern_type(TypeKind::Object(leaf_obj));

  let next_name = store.intern_name("next");
  for level in 0..depth {
    let mut shape = Shape::new();
    shape.properties.push(Property {
      key: PropKey::String(next_name),
      data: PropData {
        ty: current,
        optional: false,
        readonly: level % 2 == 0,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
    shape.properties.push(Property {
      key: PropKey::String(store.intern_name(format!("d{level:02}"))),
      data: PropData {
        ty: prim.boolean,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
    if extra_props {
      shape.properties.push(Property {
        key: PropKey::String(store.intern_name(format!("extra{level:02}"))),
        data: PropData {
          ty: prim.number,
          optional: true,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }
    let shape_id = store.intern_shape(shape);
    let obj_id = store.intern_object(types_ts_interned::ObjectType { shape: shape_id });
    current = store.intern_type(TypeKind::Object(obj_id));
  }

  current
}

fn bench_relation(c: &mut Criterion) {
  let store = TypeStore::new();
  let cache_config = CacheConfig {
    max_entries: 65_536,
    shard_count: 8,
  };

  let union_literals = intern_string_literals(&store, "u", 128);
  let union_src = store.union(union_literals.clone());
  let union_dst = store.union(union_literals[..120].to_vec());
  let union_pairs: Vec<(TypeId, TypeId)> = vec![(union_src, union_dst), (union_dst, union_src)];

  let (obj_src, obj_dst) = build_object_pair(store.as_ref(), 128, 32);
  let obj_pairs: Vec<(TypeId, TypeId)> = vec![(obj_src, obj_dst), (obj_dst, obj_src)];

  let deep_src = build_deep_object_chain(store.as_ref(), 50, true);
  let deep_dst = build_deep_object_chain(store.as_ref(), 50, false);

  let mut union_group = c.benchmark_group("types-ts-interned/relation/union_heavy");
  union_group.throughput(Throughput::Elements(union_pairs.len() as u64));

  union_group.bench_function("cold", |b| {
    b.iter_batched(
      || new_ctx(store.clone(), cache_config),
      |ctx| {
        for (src, dst) in &union_pairs {
          black_box(ctx.is_assignable(*src, *dst));
        }
      },
      BatchSize::LargeInput,
    );
  });
  {
    let ctx = new_ctx(store.clone(), cache_config);
    for (src, dst) in &union_pairs {
      black_box(ctx.is_assignable(*src, *dst));
    }
    println!("union_heavy/cold cache stats (single run):");
    print_cache_stats("  relation", ctx.cache_stats());
    print_evaluator_stats("  normalizer", ctx.normalizer_cache_stats());
  }

  let ctx = new_ctx(store.clone(), cache_config);
  for (src, dst) in &union_pairs {
    black_box(ctx.is_assignable(*src, *dst));
  }
  let before_rel = ctx.cache_stats();
  let before_norm = ctx.normalizer_cache_stats();
  union_group.bench_function("warm", |b| {
    b.iter(|| {
      for (src, dst) in &union_pairs {
        black_box(ctx.is_assignable(*src, *dst));
      }
    });
  });
  let after_rel = ctx.cache_stats();
  let after_norm = ctx.normalizer_cache_stats();
  println!("union_heavy/warm cache stats (during benchmark):");
  print_cache_stats("  relation", delta_stats(after_rel, before_rel));
  print_evaluator_stats("  normalizer", delta_evaluator_stats(after_norm, before_norm));
  union_group.finish();

  let mut obj_group = c.benchmark_group("types-ts-interned/relation/object_heavy");
  obj_group.throughput(Throughput::Elements(obj_pairs.len() as u64));

  obj_group.bench_function("cold", |b| {
    b.iter_batched(
      || new_ctx(store.clone(), cache_config),
      |ctx| {
        for (src, dst) in &obj_pairs {
          black_box(ctx.is_assignable(*src, *dst));
        }
      },
      BatchSize::LargeInput,
    );
  });
  {
    let ctx = new_ctx(store.clone(), cache_config);
    for (src, dst) in &obj_pairs {
      black_box(ctx.is_assignable(*src, *dst));
    }
    println!("object_heavy/cold cache stats (single run):");
    print_cache_stats("  relation", ctx.cache_stats());
    print_evaluator_stats("  normalizer", ctx.normalizer_cache_stats());
  }

  let ctx = new_ctx(store.clone(), cache_config);
  for (src, dst) in &obj_pairs {
    black_box(ctx.is_assignable(*src, *dst));
  }
  let before_rel = ctx.cache_stats();
  let before_norm = ctx.normalizer_cache_stats();
  obj_group.bench_function("warm", |b| {
    b.iter(|| {
      for (src, dst) in &obj_pairs {
        black_box(ctx.is_assignable(*src, *dst));
      }
    });
  });
  let after_rel = ctx.cache_stats();
  let after_norm = ctx.normalizer_cache_stats();
  println!("object_heavy/warm cache stats (during benchmark):");
  print_cache_stats("  relation", delta_stats(after_rel, before_rel));
  print_evaluator_stats("  normalizer", delta_evaluator_stats(after_norm, before_norm));
  obj_group.finish();

  let mut deep_group = c.benchmark_group("types-ts-interned/relation/deep_object_chain");
  deep_group.throughput(Throughput::Elements(1));

  deep_group.bench_function("cold", |b| {
    b.iter_batched(
      || new_ctx(store.clone(), cache_config),
      |ctx| {
        black_box(ctx.is_assignable(deep_src, deep_dst));
      },
      BatchSize::LargeInput,
    );
  });
  {
    let ctx = new_ctx(store.clone(), cache_config);
    black_box(ctx.is_assignable(deep_src, deep_dst));
    println!("deep_object_chain/cold cache stats (single run):");
    print_cache_stats("  relation", ctx.cache_stats());
    print_evaluator_stats("  normalizer", ctx.normalizer_cache_stats());
  }

  deep_group.finish();
}

criterion_group!(benches, bench_relation);
criterion_main!(benches);
