use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use std::hint::black_box;
use types_ts_interned::{
  CacheConfig, CacheStats, EvaluatorCacheStats, IntrinsicKind, MappedModifier, MappedType, PropData,
  PropKey, Property, Shape, TemplateChunk, TemplateLiteralType, TypeEvaluator, TypeExpander, TypeId,
  TypeKind, TypeOptions, TypeParamId, TypeStore,
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

struct NoopExpander;

impl TypeExpander for NoopExpander {
  fn expand(
    &self,
    _store: &TypeStore,
    _def: types_ts_interned::DefId,
    _args: &[TypeId],
  ) -> Option<types_ts_interned::ExpandedType> {
    None
  }
}

fn build_object(store: &TypeStore, prop_count: usize) -> TypeId {
  let prim = store.primitive_ids();
  let mut shape = Shape::new();

  for idx in 0..prop_count {
    let name = store.intern_name(format!("p{idx:04}"));
    let ty = match idx % 3 {
      0 => prim.string,
      1 => prim.number,
      _ => prim.boolean,
    };

    shape.properties.push(Property {
      key: PropKey::String(name),
      data: PropData {
        ty,
        optional: idx % 5 == 0,
        readonly: idx % 7 == 0,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }

  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(types_ts_interned::ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}

fn build_complex_operator_type(store: &TypeStore, prop_count: usize) -> TypeId {
  let prim = store.primitive_ids();

  let obj = build_object(store, prop_count);
  let keys = store.intern_type(TypeKind::KeyOf(obj));

  let k_param = TypeParamId(0);
  let k_ty = store.intern_type(TypeKind::TypeParam(k_param));

  let obj_k = store.intern_type(TypeKind::IndexedAccess {
    obj,
    index: k_ty,
  });

  let tag_s = store.intern_type(TypeKind::StringLiteral(store.intern_name("S")));
  let tag_n = store.intern_type(TypeKind::StringLiteral(store.intern_name("N")));
  let tag_o = store.intern_type(TypeKind::StringLiteral(store.intern_name("O")));

  // `Obj[K] extends string ? "S" : Obj[K] extends number ? "N" : "O"`
  let cond_num = store.intern_type(TypeKind::Conditional {
    check: obj_k,
    extends: prim.number,
    true_ty: tag_n,
    false_ty: tag_o,
    distributive: false,
  });
  let cond = store.intern_type(TypeKind::Conditional {
    check: obj_k,
    extends: prim.string,
    true_ty: tag_s,
    false_ty: cond_num,
    distributive: false,
  });

  let upper_k = store.intern_type(TypeKind::Intrinsic {
    kind: IntrinsicKind::Uppercase,
    ty: k_ty,
  });

  let key_remap_tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: String::new(),
    spans: vec![TemplateChunk {
      literal: String::new(),
      ty: upper_k,
    }],
  }));

  let value_tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "prop_".into(),
    spans: vec![
      TemplateChunk {
        literal: "_".into(),
        ty: upper_k,
      },
      TemplateChunk {
        literal: String::new(),
        ty: cond,
      },
    ],
  }));

  // `{ [K in keyof Obj as `...${Uppercase<K>}`]: `prop_${Uppercase<K>}_${...}` }[keyof Obj]`
  let mapped = store.intern_type(TypeKind::Mapped(MappedType {
    param: k_param,
    source: keys,
    value: value_tpl,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: Some(key_remap_tpl),
  }));

  store.intern_type(TypeKind::IndexedAccess { obj: mapped, index: keys })
}

fn build_template_cross_product(store: &TypeStore, left: usize, right: usize) -> TypeId {
  let left_members: Vec<_> = (0..left)
    .map(|idx| {
      let name = store.intern_name(format!("a{idx:02}"));
      store.intern_type(TypeKind::StringLiteral(name))
    })
    .collect();
  let right_members: Vec<_> = (0..right)
    .map(|idx| {
      let name = store.intern_name(format!("b{idx:02}"));
      store.intern_type(TypeKind::StringLiteral(name))
    })
    .collect();
  let left = store.union(left_members);
  let right = store.union(right_members);

  store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: String::new(),
    spans: vec![
      TemplateChunk {
        literal: "-".into(),
        ty: left,
      },
      TemplateChunk {
        literal: String::new(),
        ty: right,
      },
    ],
  }))
}

fn bench_evaluator(c: &mut Criterion) {
  let options = TypeOptions::default();
  let store = TypeStore::with_options(options);

  let expander = NoopExpander;
  let cache_config = CacheConfig {
    max_entries: 65_536,
    shard_count: 8,
  };

  // Pre-build and pre-intern all intermediate nodes (including template strings) so that the
  // benchmark focuses on evaluation/caching rather than one-time interner insertion.
  let complex_ty = build_complex_operator_type(store.as_ref(), 128);
  let template_ty = build_template_cross_product(store.as_ref(), 32, 32);
  {
    let mut evaluator =
      TypeEvaluator::with_cache_config(store.clone(), &expander, CacheConfig::disabled());
    black_box(evaluator.evaluate(complex_ty));
    black_box(evaluator.evaluate(template_ty));
  }

  let mut group = c.benchmark_group("types-ts-interned/evaluator");

  group.bench_function("complex_ops/cold", |b| {
    b.iter_batched(
      || TypeEvaluator::with_cache_config(store.clone(), &expander, cache_config),
      |mut evaluator| black_box(evaluator.evaluate(complex_ty)),
      BatchSize::LargeInput,
    );
  });
  {
    let mut evaluator = TypeEvaluator::with_cache_config(store.clone(), &expander, cache_config);
    black_box(evaluator.evaluate(complex_ty));
    print_evaluator_stats("complex_ops/cold cache stats (single eval)", evaluator.cache_stats());
  }

  let mut warm_evaluator = TypeEvaluator::with_cache_config(store.clone(), &expander, cache_config);
  black_box(warm_evaluator.evaluate(complex_ty));
  let before = warm_evaluator.cache_stats();
  group.bench_function("complex_ops/warm", |b| {
    b.iter(|| black_box(warm_evaluator.evaluate(complex_ty)));
  });
  let after = warm_evaluator.cache_stats();
  print_evaluator_stats(
    "complex_ops/warm cache stats (during benchmark)",
    delta_evaluator_stats(after, before),
  );

  group.bench_function("template_32x32/cold", |b| {
    b.iter_batched(
      || TypeEvaluator::with_cache_config(store.clone(), &expander, cache_config),
      |mut evaluator| black_box(evaluator.evaluate(template_ty)),
      BatchSize::LargeInput,
    );
  });
  {
    let mut evaluator = TypeEvaluator::with_cache_config(store.clone(), &expander, cache_config);
    black_box(evaluator.evaluate(template_ty));
    print_evaluator_stats(
      "template_32x32/cold cache stats (single eval)",
      evaluator.cache_stats(),
    );
  }

  group.finish();
}

criterion_group!(benches, bench_evaluator);
criterion_main!(benches);
