use std::sync::Arc;

use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use proptest::option;
use proptest::prelude::*;
use proptest::strategy::{BoxedStrategy, LazyJust, Strategy};
use types_ts_interned::{
  DefId, ExpandedType, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property,
  RelateCtx, RelateHooks, Shape, Signature, TemplateChunk, TemplateLiteralType, TupleElem,
  TypeEvaluator, TypeId, TypeKind, TypeParamId, TypeStore,
};

fn small_string() -> impl Strategy<Value = String> {
  let charset: Vec<char> = "abcdefghijklmnopqrstuvwxyz0123456789".chars().collect();
  prop::collection::vec(prop::sample::select(charset), 0..4)
    .prop_map(|chars| chars.into_iter().collect())
}

fn mapped_modifier_strategy() -> impl Strategy<Value = MappedModifier> {
  prop_oneof![
    Just(MappedModifier::Add),
    Just(MappedModifier::Remove),
    Just(MappedModifier::Preserve),
  ]
}

fn arbitrary_type_with_ref_strategy<S>(store: Arc<TypeStore>, ref_def: S) -> BoxedStrategy<TypeId>
where
  S: Strategy<Value = u32> + Clone + 'static,
{
  let primitives = store.primitive_ids();
  let bool_lit_store = store.clone();
  let number_lit_store = store.clone();
  let string_lit_store = store.clone();
  let bigint_lit_store = store.clone();
  let type_param_store = store.clone();
  let infer_store = store.clone();

  let leaf = prop_oneof![
    Just(primitives.any),
    Just(primitives.unknown),
    Just(primitives.never),
    Just(primitives.boolean),
    Just(primitives.number),
    Just(primitives.string),
    Just(primitives.bigint),
    Just(primitives.symbol),
    any::<bool>().prop_map(move |v| bool_lit_store.intern_type(TypeKind::BooleanLiteral(v))),
    (-5i16..5i16).prop_map(move |v| {
      number_lit_store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(v as f64)))
    }),
    small_string().prop_map(move |s| {
      let name = string_lit_store.intern_name(s);
      string_lit_store.intern_type(TypeKind::StringLiteral(name))
    }),
    (-3i64..3i64)
      .prop_map(move |n| bigint_lit_store.intern_type(TypeKind::BigIntLiteral(BigInt::from(n)))),
    (0u32..4)
      .prop_map(move |id| type_param_store.intern_type(TypeKind::TypeParam(TypeParamId(id)))),
    (0u32..4).prop_map(move |id| {
      infer_store.intern_type(TypeKind::Infer {
        param: TypeParamId(id),
        constraint: None,
      })
    }),
    Just(store.intern_type(TypeKind::This)),
  ];

  leaf
    .prop_recursive(4, 48, 8, move |inner| {
      let union_store = store.clone();
      let intersection_store = store.clone();
      let array_store = store.clone();
      let tuple_store = store.clone();
      let object_store = store.clone();
      let callable_store = store.clone();
      let conditional_store = store.clone();
      let mapped_store = store.clone();
      let template_store = store.clone();
      let indexed_store = store.clone();
      let keyof_store = store.clone();
      let ref_store = store.clone();
      let ref_def = ref_def.clone();

      prop_oneof![
        prop::collection::vec(inner.clone(), 1..4)
          .prop_map(move |members| union_store.union(members)),
        prop::collection::vec(inner.clone(), 1..4)
          .prop_map(move |members| intersection_store.intersection(members)),
        (inner.clone(), any::<bool>()).prop_map(move |(ty, readonly)| {
          array_store.intern_type(TypeKind::Array { ty, readonly })
        }),
        prop::collection::vec(
          (inner.clone(), any::<bool>(), any::<bool>(), any::<bool>()),
          0..4
        )
        .prop_map(move |elems| {
          let mapped_elems = elems
            .into_iter()
            .map(|(ty, optional, rest, readonly)| TupleElem {
              ty,
              optional,
              rest,
              readonly,
            })
            .collect();
          tuple_store.intern_type(TypeKind::Tuple(mapped_elems))
        }),
        prop::collection::vec(
          (
            prop::sample::select(vec!["a", "b", "c", "d", "key"]),
            inner.clone(),
            any::<bool>(),
            any::<bool>(),
            any::<bool>()
          ),
          0..3
        )
        .prop_map(move |props| {
          let mut shape = Shape::new();
          for (name, ty, optional, readonly, is_method) in props {
            shape.properties.push(Property {
              key: PropKey::String(object_store.intern_name(name)),
              data: PropData {
                ty,
                optional,
                readonly,
                accessibility: None,
                is_method,
                origin: None,
                declared_on: None,
              },
            });
          }
          let shape_id = object_store.intern_shape(shape);
          let obj_id = object_store.intern_object(ObjectType { shape: shape_id });
          object_store.intern_type(TypeKind::Object(obj_id))
        }),
        prop::collection::vec(
          (prop::collection::vec(inner.clone(), 0..3), inner.clone()),
          1..3
        )
        .prop_map(move |entries| {
          let overloads: Vec<_> = entries
            .into_iter()
            .enumerate()
            .map(|(idx, (params, ret))| {
              let param_len = params.len();
              let mut signature_params = Vec::new();
              for (param_idx, ty) in params.into_iter().enumerate() {
                signature_params.push(Param {
                  name: Some(callable_store.intern_name(format!("p{idx}_{param_idx}"))),
                  ty,
                  optional: param_idx % 2 == 0,
                  rest: param_idx + 1 == param_len,
                });
              }
              callable_store.intern_signature(Signature::new(signature_params, ret))
            })
            .collect();
          callable_store.intern_type(TypeKind::Callable { overloads })
        }),
        (
          inner.clone(),
          inner.clone(),
          inner.clone(),
          inner.clone(),
          any::<bool>()
        )
          .prop_map(move |(check, extends, true_ty, false_ty, distributive)| {
            conditional_store.intern_type(TypeKind::Conditional {
              check,
              extends,
              true_ty,
              false_ty,
              distributive,
            })
          }),
        (
          any::<u8>(),
          inner.clone(),
          inner.clone(),
          mapped_modifier_strategy(),
          mapped_modifier_strategy(),
          option::of(inner.clone()),
          option::of(inner.clone())
        )
          .prop_map(
            move |(param_seed, source, value, readonly, optional, name_type, as_type)| {
              mapped_store.intern_type(TypeKind::Mapped(MappedType {
                param: TypeParamId((param_seed % 6) as u32),
                source,
                value,
                readonly,
                optional,
                name_type,
                as_type,
              }))
            }
          ),
        (
          small_string(),
          prop::collection::vec((small_string(), inner.clone()), 0..3)
        )
          .prop_map(move |(head, spans)| {
            let spans = spans
              .into_iter()
              .map(|(literal, ty)| TemplateChunk { literal, ty })
              .collect();
            template_store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
              head,
              spans,
            }))
          },),
        (inner.clone(), inner.clone()).prop_map(move |(obj, index)| {
          indexed_store.intern_type(TypeKind::IndexedAccess { obj, index })
        }),
        inner
          .clone()
          .prop_map(move |ty| keyof_store.intern_type(TypeKind::KeyOf(ty))),
        (ref_def, prop::collection::vec(inner.clone(), 0..3)).prop_map(move |(def, args)| {
          ref_store.intern_type(TypeKind::Ref {
            def: DefId(def),
            args,
          })
        }),
      ]
    })
    .boxed()
}

fn arbitrary_type(store: Arc<TypeStore>) -> BoxedStrategy<TypeId> {
  arbitrary_type_with_ref_strategy(store, any::<u32>())
}

fn arbitrary_type_with_ref_limit(store: Arc<TypeStore>, defs: u32) -> BoxedStrategy<TypeId> {
  arbitrary_type_with_ref_strategy(store, 0u32..defs)
}

fn store_with_type() -> impl Strategy<Value = (Arc<TypeStore>, TypeId)> {
  LazyJust::new(TypeStore::new).prop_flat_map(|store| {
    let ty = arbitrary_type(store.clone());
    ty.prop_map(move |ty| (store.clone(), ty))
  })
}

fn store_with_pairs() -> impl Strategy<Value = (Arc<TypeStore>, Vec<(TypeId, TypeId)>)> {
  LazyJust::new(TypeStore::new).prop_flat_map(|store| {
    let pair = (arbitrary_type(store.clone()), arbitrary_type(store.clone()));
    prop::collection::vec(pair, 1..4).prop_map(move |pairs| (store.clone(), pairs))
  })
}

fn store_with_cyclic_pairs(
  def_count: std::ops::Range<u32>,
) -> impl Strategy<Value = (Arc<TypeStore>, Vec<(DefId, TypeId)>, Vec<(TypeId, TypeId)>)> {
  LazyJust::new(TypeStore::new).prop_flat_map(move |store| {
    def_count.clone().prop_flat_map(move |count| {
      let store = store.clone();
      let root = arbitrary_type_with_ref_limit(store.clone(), count);
      let defs = prop::collection::vec(root.clone(), count as usize..(count as usize + 1))
        .prop_map(move |defs| {
          defs
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| (DefId(idx as u32), ty))
            .collect::<Vec<_>>()
        });
      let pair = (root.clone(), root.clone());
      let pairs = prop::collection::vec(pair, 1..8);
      (defs, pairs).prop_map(move |(defs, pairs)| (store.clone(), defs, pairs))
    })
  })
}

fn store_with_cyclic_graph(
  def_count: std::ops::Range<u32>,
) -> impl Strategy<Value = (Arc<TypeStore>, TypeId, Vec<(DefId, TypeId)>)> {
  LazyJust::new(TypeStore::new).prop_flat_map(move |store| {
    def_count.clone().prop_flat_map(move |count| {
      let store = store.clone();
      let root = arbitrary_type_with_ref_limit(store.clone(), count);
      let defs = prop::collection::vec(root.clone(), count as usize..(count as usize + 1))
        .prop_map(move |defs| {
          defs
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| (DefId(idx as u32), ty))
            .collect::<Vec<_>>()
        });
      (root, defs).prop_map(move |(root, defs)| (store.clone(), root, defs))
    })
  })
}

fn store_with_defs(
  def_count: std::ops::Range<usize>,
) -> impl Strategy<Value = (Arc<TypeStore>, TypeId, Vec<(DefId, TypeId)>)> {
  LazyJust::new(TypeStore::new).prop_flat_map(move |store| {
    let root = arbitrary_type(store.clone());
    let defs = prop::collection::vec(arbitrary_type(store.clone()), def_count.clone()).prop_map(
      move |defs| {
        defs
          .into_iter()
          .enumerate()
          .map(|(idx, ty)| (DefId(idx as u32), ty))
          .collect::<Vec<_>>()
      },
    );
    (root, defs).prop_map(move |(root, defs)| (store.clone(), root, defs))
  })
}

#[derive(Debug)]
struct StaticExpander {
  defs: Vec<(DefId, TypeId)>,
}

impl types_ts_interned::TypeExpander for StaticExpander {
  fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    self
      .defs
      .iter()
      .find(|(id, _)| *id == def)
      .map(|(_, ty)| ExpandedType {
        params: Vec::new(),
        ty: *ty,
      })
  }
}

impl types_ts_interned::RelateTypeExpander for StaticExpander {
  fn expand_ref(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<TypeId> {
    self
      .defs
      .iter()
      .find(|(id, _)| *id == def)
      .map(|(_, ty)| *ty)
  }
}

fn store_with_recursive_operator_graph(
) -> impl Strategy<Value = (Arc<TypeStore>, TypeId, Vec<(DefId, TypeId)>)> {
  LazyJust::new(TypeStore::new).prop_flat_map(|store| {
    (
      small_string(),
      small_string(),
      any::<bool>(),
      mapped_modifier_strategy(),
      mapped_modifier_strategy(),
    )
      .prop_map(move |(head, suffix, distributive, readonly, optional)| {
        let primitives = store.primitive_ids();

        let def0_ref = store.intern_type(TypeKind::Ref {
          def: DefId(0),
          args: Vec::new(),
        });
        let def1_ref = store.intern_type(TypeKind::Ref {
          def: DefId(1),
          args: Vec::new(),
        });
        let def2_ref = store.intern_type(TypeKind::Ref {
          def: DefId(2),
          args: Vec::new(),
        });

        // A small recursive conditional type: `type D0 = D0 extends string ? D1 : D2`.
        let def0 = store.intern_type(TypeKind::Conditional {
          check: def0_ref,
          extends: primitives.string,
          true_ty: def1_ref,
          false_ty: def2_ref,
          distributive,
        });

        // A mapped type that depends on `keyof D2`.
        let param = TypeParamId(0);
        let def1 = store.intern_type(TypeKind::Mapped(MappedType {
          param,
          source: store.intern_type(TypeKind::KeyOf(def2_ref)),
          value: def0_ref,
          readonly,
          optional,
          name_type: None,
          as_type: None,
        }));

        // A recursive template-literal type: `type D2 = `${head}${D2}${suffix}``.
        let def2 = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
          head,
          spans: vec![TemplateChunk {
            literal: suffix,
            ty: def2_ref,
          }],
        }));

        let defs = vec![(DefId(0), def0), (DefId(1), def1), (DefId(2), def2)];
        (store.clone(), def0_ref, defs)
      })
  })
}

#[test]
fn expand_ref_no_progress_cycle_does_not_overflow() {
  // Regression test for a common "no progress" reference cycle:
  // `type A = A;` (or equivalently an expander that expands `A` to `A`).
  //
  // Historically this kind of cycle risks infinite recursion in `expand_ref`
  // callers if recursion guards are missing.
  let store = TypeStore::new();

  let self_ref = store.intern_type(TypeKind::Ref {
    def: DefId(0),
    args: Vec::new(),
  });
  let defs = vec![(DefId(0), self_ref)];
  let expander = StaticExpander { defs };

  let mut evaluator = TypeEvaluator::new(store.clone(), &expander).with_depth_limit(128);
  let evaluated = evaluator.evaluate(self_ref);
  assert_eq!(store.canon(evaluated), store.canon(self_ref));

  let hooks = RelateHooks {
    expander: Some(&expander),
    is_same_origin_private_member: None,
  };
  let ctx = RelateCtx::with_hooks(store.clone(), store.options(), hooks);
  let prim = store.primitive_ids();
  let res1 = ctx.is_assignable(self_ref, prim.number);
  let res2 = ctx.is_assignable(self_ref, prim.number);
  assert_eq!(res1, res2);
  assert_eq!(ctx.explain_assignable(self_ref, prim.number).result, res1);

  let res3 = ctx.is_assignable(prim.number, self_ref);
  assert_eq!(ctx.explain_assignable(prim.number, self_ref).result, res3);
}

proptest! {
  #![proptest_config(ProptestConfig::with_cases(64))]

  #[test]
  fn canon_is_idempotent((store, ty) in store_with_type()) {
    let once = store.canon(ty);
    let twice = store.canon(once);
    prop_assert_eq!(once, twice);
  }

  #[test]
  fn relation_engine_is_stable((store, pairs) in store_with_pairs()) {
    let ctx = RelateCtx::new(store.clone(), store.options());
    let mut expected = Vec::new();
    for (src, dst) in pairs.iter() {
      expected.push(ctx.is_assignable(*src, *dst));
    }

    for ((src, dst), expect) in pairs.iter().zip(expected.iter()) {
      prop_assert_eq!(ctx.is_assignable(*src, *dst), *expect);
      prop_assert_eq!(ctx.explain_assignable(*src, *dst).result, *expect);
    }

    let fresh_ctx = RelateCtx::new(store.clone(), store.options());
    for ((src, dst), expect) in pairs.iter().zip(expected.iter()) {
      prop_assert_eq!(fresh_ctx.is_assignable(*src, *dst), *expect);
    }
  }

  #[test]
  fn relation_engine_terminates_on_cyclic_graphs((store, defs, pairs) in store_with_cyclic_pairs(1..6)) {
    let expander = StaticExpander { defs: defs.clone() };
    let hooks = RelateHooks {
      expander: Some(&expander),
      is_same_origin_private_member: None,
    };
    let ctx = RelateCtx::with_hooks(store.clone(), store.options(), hooks).with_step_limit(20_000);
    let mut expected = Vec::new();
    for (src, dst) in pairs.iter() {
      expected.push(ctx.is_assignable(*src, *dst));
      prop_assert!(ctx.step_count() < 20_000);
    }

    for ((src, dst), expect) in pairs.iter().zip(expected.iter()) {
      prop_assert_eq!(ctx.is_assignable(*src, *dst), *expect);
      prop_assert!(ctx.step_count() < 20_000);
      prop_assert_eq!(ctx.explain_assignable(*src, *dst).result, *expect);
      prop_assert!(ctx.step_count() < 20_000);
    }

    // Ensure determinism is maintained with fresh caches as well.
    let hooks = RelateHooks {
      expander: Some(&expander),
      is_same_origin_private_member: None,
    };
    let fresh_ctx =
      RelateCtx::with_hooks(store.clone(), store.options(), hooks).with_step_limit(20_000);
    for ((src, dst), expect) in pairs.iter().zip(expected.iter()) {
      prop_assert_eq!(fresh_ctx.is_assignable(*src, *dst), *expect);
      prop_assert!(fresh_ctx.step_count() < 20_000);
    }
  }

  #[test]
  fn evaluator_terminates_on_random_graphs((store, root, defs) in store_with_defs(0..4)) {
    let expander = StaticExpander { defs: defs.clone() };
    let mut evaluator = TypeEvaluator::new(store.clone(), &expander)
      .with_depth_limit(64)
      .with_step_limit(10_000);
    let first = evaluator.evaluate(root);
    prop_assert!(evaluator.step_count() < 10_000);
    let second = evaluator.evaluate(root);
    prop_assert!(evaluator.step_count() < 10_000);
    prop_assert_eq!(store.canon(first), store.canon(second));

    for (_, ty) in defs {
      let mut eval = TypeEvaluator::new(store.clone(), &expander)
        .with_depth_limit(64)
        .with_step_limit(10_000);
      let _ = eval.evaluate(ty);
      prop_assert!(eval.step_count() < 10_000);
    }
  }

  #[test]
  fn relation_engine_terminates_on_random_graphs((store, pairs) in store_with_pairs()) {
    let ctx = RelateCtx::new(store.clone(), store.options()).with_step_limit(20_000);
    for (src, dst) in pairs {
      let _ = ctx.is_assignable(src, dst);
      prop_assert!(ctx.step_count() < 20_000);
    }
  }

  #[test]
  fn evaluator_terminates_on_cyclic_graphs((store, root, defs) in store_with_cyclic_graph(1..6)) {
    let expander = StaticExpander { defs: defs.clone() };
    let mut evaluator = TypeEvaluator::new(store.clone(), &expander)
      .with_depth_limit(128)
      .with_step_limit(10_000);
    let first = evaluator.evaluate(root);
    prop_assert!(evaluator.step_count() < 10_000);
    let second = evaluator.evaluate(root);
    prop_assert!(evaluator.step_count() < 10_000);
    prop_assert_eq!(store.canon(first), store.canon(second));

    for (_, ty) in defs {
      let mut eval = TypeEvaluator::new(store.clone(), &expander)
        .with_depth_limit(128)
        .with_step_limit(10_000);
      let _ = eval.evaluate(ty);
      prop_assert!(eval.step_count() < 10_000);
    }
  }

  #[test]
  fn evaluator_handles_recursive_conditional_mapped_and_template_types((store, root, defs) in store_with_recursive_operator_graph()) {
    let expander = StaticExpander { defs: defs.clone() };
    let mut evaluator = TypeEvaluator::new(store.clone(), &expander)
      .with_depth_limit(128)
      .with_step_limit(10_000);
    let first = evaluator.evaluate(root);
    prop_assert!(evaluator.step_count() < 10_000);
    let second = evaluator.evaluate(root);
    prop_assert!(evaluator.step_count() < 10_000);
    prop_assert_eq!(store.canon(first), store.canon(second));
  }
}
