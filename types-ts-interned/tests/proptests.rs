use std::sync::Arc;

use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use proptest::option;
use proptest::prelude::*;
use proptest::strategy::{BoxedStrategy, LazyJust, Strategy};
use types_ts_interned::{
  DefId, ExpandedType, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property,
  RelateCtx, Shape, Signature, TemplateChunk, TemplateLiteralType, TupleElem, TypeEvaluator,
  TypeId, TypeKind, TypeParamId, TypeStore,
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

fn arbitrary_type(store: Arc<TypeStore>) -> BoxedStrategy<TypeId> {
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
        (any::<u32>(), prop::collection::vec(inner.clone(), 0..3)).prop_map(move |(def, args)| {
          ref_store.intern_type(TypeKind::Ref {
            def: DefId(def),
            args,
          })
        }),
      ]
    })
    .boxed()
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
}
