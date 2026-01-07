use std::sync::{Arc, Barrier};
use std::thread;

use ordered_float::OrderedFloat;
use types_ts_interned::{
  CacheConfig, DefId, EvaluatorCaches, ExpandedType, Indexer, IntrinsicKind, MappedModifier,
  MappedType, ObjectType, Param, PropData, PropKey, Property, RelateCtx, RelationCache, Shape,
  Signature, TemplateChunk, TemplateLiteralType, TypeEvaluator, TypeExpander, TypeId, TypeKind,
  TypeOptions, TypeParamId, TypeStore,
};

fn shuffle<T>(items: &mut [T], mut seed: u64) {
  if items.is_empty() {
    return;
  }

  for i in (1..items.len()).rev() {
    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    let j = (seed >> 32) as usize % (i + 1);
    items.swap(i, j);
  }
}

fn prop_data(ty: TypeId, optional: bool, readonly: bool) -> PropData {
  PropData {
    ty,
    optional,
    readonly,
    accessibility: None,
    is_method: false,
    origin: None,
    declared_on: None,
  }
}

#[derive(Debug, Clone)]
struct TestExpander {
  box_def: DefId,
  box_param: TypeParamId,
  box_ty: TypeId,
  maybe_upper_def: DefId,
  maybe_upper_param: TypeParamId,
  maybe_upper_ty: TypeId,
}

impl TestExpander {
  fn new(store: &Arc<TypeStore>) -> Self {
    let primitives = store.primitive_ids();

    let box_def = DefId(1);
    let box_param = TypeParamId(100);
    let value_name = store.intern_name("value");
    let box_param_ty = store.intern_type(TypeKind::TypeParam(box_param));
    let box_shape = Shape {
      properties: vec![Property {
        key: PropKey::String(value_name),
        data: prop_data(box_param_ty, false, false),
      }],
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      indexers: Vec::new(),
    };
    let box_shape_id = store.intern_shape(box_shape);
    let box_obj = store.intern_object(ObjectType {
      shape: box_shape_id,
    });
    let box_ty = store.intern_type(TypeKind::Object(box_obj));

    let maybe_upper_def = DefId(2);
    let maybe_upper_param = TypeParamId(101);
    let maybe_upper_param_ty = store.intern_type(TypeKind::TypeParam(maybe_upper_param));
    let upper = store.intern_type(TypeKind::Intrinsic {
      kind: IntrinsicKind::Uppercase,
      ty: maybe_upper_param_ty,
    });
    let maybe_upper_ty = store.intern_type(TypeKind::Conditional {
      check: maybe_upper_param_ty,
      extends: primitives.string,
      true_ty: upper,
      false_ty: maybe_upper_param_ty,
      distributive: true,
    });

    Self {
      box_def,
      box_param,
      box_ty,
      maybe_upper_def,
      maybe_upper_param,
      maybe_upper_ty,
    }
  }
}

impl TypeExpander for TestExpander {
  fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    if def == self.box_def {
      Some(ExpandedType {
        params: vec![self.box_param],
        ty: self.box_ty,
      })
    } else if def == self.maybe_upper_def {
      Some(ExpandedType {
        params: vec![self.maybe_upper_param],
        ty: self.maybe_upper_ty,
      })
    } else {
      None
    }
  }
}

fn build_evaluator_inputs(store: &Arc<TypeStore>, expander: &TestExpander) -> Vec<TypeId> {
  let primitives = store.primitive_ids();

  let foo = store.intern_name("foo");
  let bar = store.intern_name("bar");
  let baz = store.intern_name("baz");

  let obj_shape = Shape {
    properties: vec![
      Property {
        key: PropKey::String(foo),
        data: prop_data(primitives.number, false, false),
      },
      Property {
        key: PropKey::String(bar),
        data: prop_data(primitives.string, true, true),
      },
      Property {
        key: PropKey::String(baz),
        data: prop_data(primitives.boolean, false, true),
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  };
  let obj_shape_id = store.intern_shape(obj_shape);
  let obj_id = store.intern_object(ObjectType {
    shape: obj_shape_id,
  });
  let obj_ty = store.intern_type(TypeKind::Object(obj_id));

  let keyof_obj = store.intern_type(TypeKind::KeyOf(obj_ty));
  let tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "pre_".into(),
    spans: vec![TemplateChunk {
      literal: "_suf".into(),
      ty: keyof_obj,
    }],
  }));
  let upper_tpl = store.intern_type(TypeKind::Intrinsic {
    kind: IntrinsicKind::Uppercase,
    ty: tpl,
  });

  let mapped_param = TypeParamId(200);
  let mapped_param_ty = store.intern_type(TypeKind::TypeParam(mapped_param));
  let foo_lit = store.intern_type(TypeKind::StringLiteral(foo));
  let cond = store.intern_type(TypeKind::Conditional {
    check: mapped_param_ty,
    extends: foo_lit,
    true_ty: primitives.number,
    false_ty: primitives.string,
    distributive: true,
  });
  let mapped_plain = store.intern_type(TypeKind::Mapped(MappedType {
    param: mapped_param,
    source: keyof_obj,
    value: cond,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: None,
  }));
  let as_upper = store.intern_type(TypeKind::Intrinsic {
    kind: IntrinsicKind::Uppercase,
    ty: mapped_param_ty,
  });
  let mapped_remap = store.intern_type(TypeKind::Mapped(MappedType {
    param: mapped_param,
    source: keyof_obj,
    value: cond,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: Some(as_upper),
  }));

  let indexed_foo = store.intern_type(TypeKind::IndexedAccess {
    obj: mapped_plain,
    index: foo_lit,
  });
  let indexed_bar = store.intern_type(TypeKind::IndexedAccess {
    obj: mapped_plain,
    index: store.intern_type(TypeKind::StringLiteral(bar)),
  });
  let indexed_union = store.intern_type(TypeKind::IndexedAccess {
    obj: mapped_plain,
    index: store.union(vec![
      foo_lit,
      store.intern_type(TypeKind::StringLiteral(bar)),
    ]),
  });
  let keyof_remap = store.intern_type(TypeKind::KeyOf(mapped_remap));

  let mut out = vec![
    obj_ty,
    keyof_obj,
    tpl,
    upper_tpl,
    mapped_plain,
    mapped_remap,
    indexed_foo,
    indexed_bar,
    indexed_union,
    keyof_remap,
  ];

  let value_key = store.intern_type(TypeKind::StringLiteral(store.intern_name("value")));

  for i in 0..24u32 {
    let name = store.intern_name(format!("s{i}"));
    let str_lit = store.intern_type(TypeKind::StringLiteral(name));
    let num_lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(i as f64)));
    let union = store.union(vec![str_lit, num_lit]);
    let maybe = store.intern_type(TypeKind::Ref {
      def: expander.maybe_upper_def,
      args: vec![union],
    });
    let boxed = store.intern_type(TypeKind::Ref {
      def: expander.box_def,
      args: vec![maybe],
    });
    let unboxed = store.intern_type(TypeKind::IndexedAccess {
      obj: boxed,
      index: value_key,
    });
    let template = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
      head: format!("val{i}_"),
      spans: vec![TemplateChunk {
        literal: "_end".into(),
        ty: unboxed,
      }],
    }));
    out.extend([union, maybe, boxed, unboxed, template]);
  }

  out
}

#[test]
fn evaluator_caches_are_deterministic_under_concurrency() {
  const THREADS: usize = 8;
  const ROUNDS: usize = 4;

  let store = TypeStore::new();
  let expander = Arc::new(TestExpander::new(&store));
  let inputs = Arc::new(build_evaluator_inputs(&store, &expander));

  let baseline = {
    let mut evaluator = TypeEvaluator::new(store.clone(), expander.as_ref());
    inputs
      .iter()
      .copied()
      .map(|ty| evaluator.evaluate(ty))
      .collect::<Vec<_>>()
  };

  let shared_caches = EvaluatorCaches::new(CacheConfig {
    max_entries: 32,
    shard_count: 4,
  });

  let barrier = Arc::new(Barrier::new(THREADS));
  let mut handles = Vec::with_capacity(THREADS);
  for thread_idx in 0..THREADS {
    let store = store.clone();
    let expander = expander.clone();
    let caches = shared_caches.clone();
    let barrier = barrier.clone();
    let inputs = inputs.clone();
    handles.push(thread::spawn(move || {
      let mut evaluator = TypeEvaluator::with_caches(store, expander.as_ref(), caches);
      barrier.wait();

      let mut out = vec![TypeId(0); inputs.len()];
      for round in 0..ROUNDS {
        let mut indices: Vec<usize> = (0..inputs.len()).collect();
        let seed = (thread_idx as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15)
          ^ (round as u64 + 1).wrapping_mul(0x517c_c1b7_2722_0a95);
        shuffle(&mut indices, seed);
        for idx in indices {
          out[idx] = evaluator.evaluate(inputs[idx]);
        }
      }
      out
    }));
  }

  for (thread_idx, handle) in handles.into_iter().enumerate() {
    let results = handle.join().expect("thread panicked");
    assert_eq!(
      results, baseline,
      "thread {thread_idx} produced a different evaluation sequence"
    );
  }
}

fn build_relation_pairs(store: &Arc<TypeStore>) -> Vec<(TypeId, TypeId)> {
  let primitives = store.primitive_ids();

  let a = store.intern_name("a");
  let b = store.intern_name("b");
  let c = store.intern_name("c");

  let obj_a_shape = Shape {
    properties: vec![
      Property {
        key: PropKey::String(a),
        data: prop_data(primitives.number, false, false),
      },
      Property {
        key: PropKey::String(b),
        data: prop_data(primitives.string, false, false),
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  };
  let obj_a_shape_id = store.intern_shape(obj_a_shape);
  let obj_a_id = store.intern_object(ObjectType {
    shape: obj_a_shape_id,
  });
  let obj_a_ty = store.intern_type(TypeKind::Object(obj_a_id));

  let obj_wide_shape = Shape {
    properties: vec![
      Property {
        key: PropKey::String(a),
        data: prop_data(
          store.union(vec![primitives.number, primitives.string]),
          false,
          false,
        ),
      },
      Property {
        key: PropKey::String(b),
        data: prop_data(primitives.string, false, false),
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  };
  let obj_wide_shape_id = store.intern_shape(obj_wide_shape);
  let obj_wide_id = store.intern_object(ObjectType {
    shape: obj_wide_shape_id,
  });
  let obj_wide_ty = store.intern_type(TypeKind::Object(obj_wide_id));

  let obj_indexer_shape = Shape {
    properties: vec![Property {
      key: PropKey::String(c),
      data: prop_data(primitives.boolean, false, false),
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: vec![Indexer {
      key_type: primitives.string,
      value_type: primitives.number,
      readonly: false,
    }],
  };
  let obj_indexer_shape_id = store.intern_shape(obj_indexer_shape);
  let obj_indexer_id = store.intern_object(ObjectType {
    shape: obj_indexer_shape_id,
  });
  let obj_indexer_ty = store.intern_type(TypeKind::Object(obj_indexer_id));

  let x = store.intern_name("x");
  let sig1 = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(x),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    primitives.string,
  ));
  let sig2 = store.intern_signature(Signature::new(
    vec![Param {
      name: Some(x),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    store.union(vec![primitives.string, primitives.number]),
  ));
  let callable1 = store.intern_type(TypeKind::Callable {
    overloads: vec![sig1],
  });
  let callable2 = store.intern_type(TypeKind::Callable {
    overloads: vec![sig2],
  });

  let union_objects = store.union(vec![obj_a_ty, obj_indexer_ty]);
  let intersection_objects = store.intersection(vec![obj_wide_ty, obj_indexer_ty]);

  let keyof_obj_a = store.intern_type(TypeKind::KeyOf(obj_a_ty));
  let template_keys = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "get_".into(),
    spans: vec![TemplateChunk {
      literal: "".into(),
      ty: keyof_obj_a,
    }],
  }));
  let indexed_a = store.intern_type(TypeKind::IndexedAccess {
    obj: obj_a_ty,
    index: store.intern_type(TypeKind::StringLiteral(a)),
  });
  let indexed_b = store.intern_type(TypeKind::IndexedAccess {
    obj: obj_a_ty,
    index: store.intern_type(TypeKind::StringLiteral(b)),
  });

  let mapped_param = TypeParamId(300);
  let mapped_param_ty = store.intern_type(TypeKind::TypeParam(mapped_param));
  let mapped_value = store.intern_type(TypeKind::Conditional {
    check: mapped_param_ty,
    extends: store.intern_type(TypeKind::StringLiteral(a)),
    true_ty: primitives.number,
    false_ty: primitives.boolean,
    distributive: true,
  });
  let mapped_obj = store.intern_type(TypeKind::Mapped(MappedType {
    param: mapped_param,
    source: keyof_obj_a,
    value: mapped_value,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Add,
    name_type: None,
    as_type: None,
  }));

  let cond = store.intern_type(TypeKind::Conditional {
    check: store.union(vec![
      store.intern_type(TypeKind::StringLiteral(a)),
      store.intern_type(TypeKind::StringLiteral(b)),
    ]),
    extends: store.intern_type(TypeKind::StringLiteral(a)),
    true_ty: primitives.number,
    false_ty: primitives.string,
    distributive: true,
  });

  let type_pool = vec![
    primitives.any,
    primitives.unknown,
    primitives.never,
    primitives.null,
    primitives.undefined,
    primitives.boolean,
    primitives.number,
    primitives.string,
    obj_a_ty,
    obj_wide_ty,
    obj_indexer_ty,
    callable1,
    callable2,
    union_objects,
    intersection_objects,
    keyof_obj_a,
    template_keys,
    indexed_a,
    indexed_b,
    mapped_obj,
    cond,
  ];

  let mut pairs = Vec::new();
  for (src_idx, src) in type_pool.iter().copied().enumerate() {
    for salt in 0..6usize {
      let dst_idx = (src_idx
        .wrapping_mul(7)
        .wrapping_add(salt.wrapping_mul(13))
        .wrapping_add(3))
        % type_pool.len();
      pairs.push((src, type_pool[dst_idx]));
    }
  }
  pairs
}

#[test]
fn relate_caches_and_normalizer_caches_are_deterministic_under_concurrency() {
  const THREADS: usize = 8;
  const ROUNDS: usize = 4;

  let store = TypeStore::new();
  let options = TypeOptions::default();
  let pairs = Arc::new(build_relation_pairs(&store));

  let baseline = {
    let ctx = RelateCtx::new(store.clone(), options);
    pairs
      .iter()
      .copied()
      .map(|(src, dst)| ctx.is_assignable(src, dst))
      .collect::<Vec<_>>()
  };

  let shared_relation_cache = RelationCache::new(CacheConfig {
    max_entries: 64,
    shard_count: 4,
  });
  let shared_normalizer_caches = EvaluatorCaches::new(CacheConfig {
    max_entries: 64,
    shard_count: 4,
  });

  let barrier = Arc::new(Barrier::new(THREADS));
  let mut handles = Vec::with_capacity(THREADS);
  for thread_idx in 0..THREADS {
    let store = store.clone();
    let pairs = pairs.clone();
    let cache = shared_relation_cache.clone();
    let normalizer_caches = shared_normalizer_caches.clone();
    let barrier = barrier.clone();
    handles.push(thread::spawn(move || {
      let ctx = RelateCtx::with_hooks_cache_and_normalizer_caches(
        store,
        options,
        Default::default(),
        cache,
        normalizer_caches,
      );
      barrier.wait();

      let mut out = vec![false; pairs.len()];
      for round in 0..ROUNDS {
        let mut indices: Vec<usize> = (0..pairs.len()).collect();
        let seed = (thread_idx as u64 + 1).wrapping_mul(0xc2b2_ae3d_27d4_eb4f)
          ^ (round as u64 + 1).wrapping_mul(0x1656_67b1_9e37_79f9);
        shuffle(&mut indices, seed);
        for idx in indices {
          let (src, dst) = pairs[idx];
          out[idx] = ctx.is_assignable(src, dst);
        }
      }

      out
    }));
  }

  for (thread_idx, handle) in handles.into_iter().enumerate() {
    let results = handle.join().expect("thread panicked");
    assert_eq!(
      results, baseline,
      "thread {thread_idx} produced a different relation result sequence"
    );
  }
}
