use ordered_float::OrderedFloat;
use types_ts_interned::{
  CacheConfig, CacheStats, EvaluatorCaches, ObjectType, PropData, PropKey, Property, RelateCtx,
  RelationCache, Shape, TypeEvaluator, TypeExpander, TypeKind, TypeOptions, TypeStore,
};

fn default_options() -> TypeOptions {
  TypeOptions::default()
}

#[test]
fn relation_cache_is_bounded_and_evicts() {
  let store = TypeStore::new();
  let config = CacheConfig {
    max_entries: 4,
    shard_count: 1,
  };
  let ctx = RelateCtx::with_hooks_and_cache(
    store.clone(),
    default_options(),
    Default::default(),
    RelationCache::new(config),
  );
  let primitives = store.primitive_ids();

  for i in 0..32 {
    let lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat(i as f64)));
    assert!(ctx.is_assignable(lit, primitives.number));
  }

  let stats = ctx.cache_stats();
  assert!(stats.evictions > 0, "expected relation cache evictions");
  assert!(
    ctx.cache_len() <= config.max_entries,
    "relation cache exceeded bound"
  );
}

#[test]
fn relation_cache_eviction_does_not_change_results() {
  let store = TypeStore::new();
  let config = CacheConfig {
    max_entries: 2,
    shard_count: 1,
  };
  let primitives = store.primitive_ids();
  let pairs: Vec<_> = (0..12)
    .flat_map(|i| {
      let lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat(i as f64)));
      let string_target =
        store.intern_type(TypeKind::StringLiteral(store.intern_name(i.to_string())));
      [
        (lit, primitives.number),
        (lit, string_target),
        (primitives.string, lit),
      ]
    })
    .collect();

  let first_ctx = RelateCtx::with_cache_config(store.clone(), default_options(), config);
  let first: Vec<_> = pairs
    .iter()
    .map(|(a, b)| first_ctx.is_assignable(*a, *b))
    .collect();

  let second_ctx = RelateCtx::with_cache_config(store.clone(), default_options(), config);
  let second: Vec<_> = pairs
    .iter()
    .map(|(a, b)| second_ctx.is_assignable(*a, *b))
    .collect();

  assert_eq!(first, second, "eviction should not affect relation results");
  assert!(
    first_ctx.cache_stats().evictions > 0 || second_ctx.cache_stats().evictions > 0,
    "expected eviction under tight cache bound"
  );
}

struct NoopExpander;

impl TypeExpander for NoopExpander {
  fn expand(
    &self,
    _store: &TypeStore,
    _def: types_ts_interned::DefId,
    _args: &[types_ts_interned::TypeId],
  ) -> Option<types_ts_interned::ExpandedType> {
    None
  }
}

#[test]
fn evaluator_cache_eviction_is_bounded_and_deterministic() {
  let store = TypeStore::new();
  let config = CacheConfig {
    max_entries: 3,
    shard_count: 1,
  };
  let expander = NoopExpander;

  let caches = EvaluatorCaches::new(config);
  let mut evaluator = TypeEvaluator::with_caches(store.clone(), &expander, caches.clone());

  let inputs: Vec<_> = (0..16)
    .map(|i| {
      store.intern_type(TypeKind::Array {
        ty: store.intern_type(TypeKind::NumberLiteral(OrderedFloat(i as f64))),
        readonly: false,
      })
    })
    .collect();

  let first: Vec<_> = inputs.iter().map(|ty| evaluator.evaluate(*ty)).collect();

  let mut second_eval = TypeEvaluator::with_cache_config(store.clone(), &expander, config);
  let second: Vec<_> = inputs.iter().map(|ty| second_eval.evaluate(*ty)).collect();

  assert_eq!(
    first, second,
    "evictions must not change evaluation results"
  );

  let stats = evaluator.cache_stats();
  let stats2 = second_eval.cache_stats();
  assert!(
    stats.eval.evictions > 0
      || stats.references.evictions > 0
      || stats2.eval.evictions > 0
      || stats2.references.evictions > 0,
    "evaluation cache should evict under tight bounds"
  );
}

#[test]
fn evaluator_caches_can_be_cleared() {
  let store = TypeStore::new();
  let config = CacheConfig {
    max_entries: 2,
    shard_count: 1,
  };
  let expander = NoopExpander;
  let mut evaluator = TypeEvaluator::with_cache_config(store.clone(), &expander, config);

  let array = store.intern_type(TypeKind::Array {
    ty: store.primitive_ids().number,
    readonly: false,
  });
  let _ = evaluator.evaluate(array);
  let before = evaluator.cache_stats();
  assert!(
    before.eval.insertions > 0 || before.references.insertions > 0,
    "evaluation should populate caches"
  );

  evaluator.clear_caches();
  let cleared = evaluator.cache_stats();
  assert_eq!(cleared.eval, CacheStats::default());
  assert_eq!(cleared.references, CacheStats::default());
}

#[test]
fn caches_can_be_cleared_and_reused() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let cache = RelationCache::default();
  let ctx = RelateCtx::with_cache(store.clone(), default_options(), cache.clone());

  assert!(ctx.is_assignable(primitives.number, primitives.number));
  assert!(cache.len() > 0);

  cache.clear();
  assert_eq!(cache.len(), 0, "clearing should drop cached entries");
  assert_eq!(
    cache.stats(),
    CacheStats::default(),
    "clearing should reset statistics"
  );

  assert!(ctx.is_assignable(primitives.number, primitives.number));
  assert_eq!(cache.stats().hits, 0, "fresh cache should start cold");
}

#[test]
fn relate_ctx_normalizer_caches_are_reused_across_relation_checks() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let ctx = RelateCtx::new(store.clone(), default_options());

  let key = store.intern_name("a");
  let mut shape = Shape::new();
  shape.properties.push(Property {
    key: PropKey::String(key),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  let obj_ty = store.intern_type(TypeKind::Object(obj_id));

  let index_ty = store.intern_type(TypeKind::StringLiteral(key));
  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: obj_ty,
    index: index_ty,
  });

  assert!(ctx.is_assignable(indexed, primitives.number));
  let first = ctx.normalizer_cache_stats();
  assert!(
    first.eval.insertions > 0,
    "expected normalization to populate eval cache: {first:?}"
  );

  ctx.clear_cache();
  assert!(ctx.is_assignable(indexed, primitives.number));
  let second = ctx.normalizer_cache_stats();
  assert!(
    second.eval.hits > first.eval.hits,
    "expected cache hits to increase on repeated normalization: first={first:?}, second={second:?}"
  );
}

#[test]
fn relate_ctx_normalizer_caches_can_be_shared_across_contexts() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let config = CacheConfig {
    max_entries: 16,
    shard_count: 1,
  };
  let shared_caches = EvaluatorCaches::new(config);

  let ctx1 = RelateCtx::with_hooks_cache_and_normalizer_caches(
    store.clone(),
    default_options(),
    Default::default(),
    RelationCache::default(),
    shared_caches.clone(),
  );
  let ctx2 = RelateCtx::with_hooks_cache_and_normalizer_caches(
    store.clone(),
    default_options(),
    Default::default(),
    RelationCache::default(),
    shared_caches.clone(),
  );

  let key = store.intern_name("a");
  let mut shape = Shape::new();
  shape.properties.push(Property {
    key: PropKey::String(key),
    data: PropData {
      ty: primitives.number,
      optional: false,
      readonly: false,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  let obj_ty = store.intern_type(TypeKind::Object(obj_id));

  let index_ty = store.intern_type(TypeKind::StringLiteral(key));
  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: obj_ty,
    index: index_ty,
  });

  assert!(ctx1.is_assignable(indexed, primitives.number));
  let first = ctx1.normalizer_cache_stats();
  assert!(
    first.eval.insertions > 0,
    "expected normalization to populate shared eval cache: {first:?}"
  );

  assert!(ctx2.is_assignable(indexed, primitives.number));
  let second = ctx2.normalizer_cache_stats();
  assert!(
    second.eval.hits > first.eval.hits,
    "expected shared cache hits to increase across contexts: first={first:?}, second={second:?}"
  );
}
