//! Algebraic property tests for `types-ts-interned`.
//!
//! Expectations are derived from the documented laws in
//! [`wiki/crates/types-ts-interned.md`] (TypeStore interning / ACI canonicalization)
//! and [`wiki/architecture/determinism.md`] (content-addressed, order-independent IDs),
//! not from mirroring current implementation quirks.
//!
//! Bounded generators: depth ≤ 4, breadth ≤ 4. Case counts stay modest so the
//! suite remains well under ~2 minutes.

use std::cmp::Ordering;
use std::sync::Arc;

use ordered_float::OrderedFloat;
use proptest::prelude::*;
use proptest::strategy::{BoxedStrategy, Just, Strategy};
use types_ts_interned::{
  ObjectType, PropData, PropKey, Property, RelateCtx, Shape, TupleElem, TypeId, TypeKind, TypeStore,
};

/// Max nesting depth for generated type trees.
const MAX_DEPTH: u32 = 4;
/// Max union/intersection/tuple/object breadth.
const MAX_BREADTH: usize = 4;

/// Construction recipe independent of any particular [`TypeStore`].
/// Replaying the same recipe on two fresh stores is the content-addressing oracle.
#[derive(Clone, Debug, PartialEq, Eq)]
enum TypeRecipe {
  Any,
  Unknown,
  Never,
  Void,
  Null,
  Undefined,
  Boolean,
  Number,
  String,
  BigInt,
  Symbol,
  BoolLit(bool),
  NumberLit(i16),
  StringLit(&'static str),
  Array {
    elem: Box<TypeRecipe>,
    readonly: bool,
  },
  Tuple {
    elems: Vec<TypeRecipe>,
  },
  Union {
    members: Vec<TypeRecipe>,
  },
  Intersection {
    members: Vec<TypeRecipe>,
  },
  Object {
    props: Vec<ObjProp>,
  },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ObjProp {
  name: &'static str,
  ty: TypeRecipe,
  optional: bool,
  readonly: bool,
}

const PROP_NAMES: &[&str] = &["a", "b", "c", "d", "key", "x", "y", "z"];
const STR_LIT_POOL: &[&str] = &["", "a", "b", "foo", "bar", "0", "x"];

fn materialize(store: &TypeStore, recipe: &TypeRecipe) -> TypeId {
  let prim = store.primitive_ids();
  match recipe {
    TypeRecipe::Any => prim.any,
    TypeRecipe::Unknown => prim.unknown,
    TypeRecipe::Never => prim.never,
    TypeRecipe::Void => prim.void,
    TypeRecipe::Null => prim.null,
    TypeRecipe::Undefined => prim.undefined,
    TypeRecipe::Boolean => prim.boolean,
    TypeRecipe::Number => prim.number,
    TypeRecipe::String => prim.string,
    TypeRecipe::BigInt => prim.bigint,
    TypeRecipe::Symbol => prim.symbol,
    TypeRecipe::BoolLit(v) => store.intern_type(TypeKind::BooleanLiteral(*v)),
    TypeRecipe::NumberLit(v) => {
      store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(*v as f64)))
    }
    TypeRecipe::StringLit(s) => {
      let name = store.intern_name(*s);
      store.intern_type(TypeKind::StringLiteral(name))
    }
    TypeRecipe::Array { elem, readonly } => {
      let ty = materialize(store, elem);
      store.intern_type(TypeKind::Array {
        ty,
        readonly: *readonly,
      })
    }
    TypeRecipe::Tuple { elems } => {
      let mapped = elems
        .iter()
        .map(|e| TupleElem {
          ty: materialize(store, e),
          optional: false,
          rest: false,
          readonly: false,
        })
        .collect();
      store.intern_type(TypeKind::Tuple(mapped))
    }
    TypeRecipe::Union { members } => {
      let ids = members.iter().map(|m| materialize(store, m)).collect();
      store.union(ids)
    }
    TypeRecipe::Intersection { members } => {
      let ids = members.iter().map(|m| materialize(store, m)).collect();
      store.intersection(ids)
    }
    TypeRecipe::Object { props } => {
      let mut shape = Shape::new();
      for p in props {
        shape.properties.push(Property {
          key: PropKey::String(store.intern_name(p.name)),
          data: PropData {
            ty: materialize(store, &p.ty),
            optional: p.optional,
            readonly: p.readonly,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(ObjectType { shape: shape_id });
      store.intern_type(TypeKind::Object(obj_id))
    }
  }
}

fn leaf_recipe() -> impl Strategy<Value = TypeRecipe> {
  prop_oneof![
    Just(TypeRecipe::Any),
    Just(TypeRecipe::Unknown),
    Just(TypeRecipe::Never),
    Just(TypeRecipe::Void),
    Just(TypeRecipe::Null),
    Just(TypeRecipe::Undefined),
    Just(TypeRecipe::Boolean),
    Just(TypeRecipe::Number),
    Just(TypeRecipe::String),
    Just(TypeRecipe::BigInt),
    Just(TypeRecipe::Symbol),
    any::<bool>().prop_map(TypeRecipe::BoolLit),
    (-5i16..5i16).prop_map(TypeRecipe::NumberLit),
    prop::sample::select(STR_LIT_POOL.to_vec()).prop_map(|s| TypeRecipe::StringLit(s)),
  ]
}

fn type_recipe() -> BoxedStrategy<TypeRecipe> {
  leaf_recipe()
    .prop_recursive(MAX_DEPTH, 32, MAX_BREADTH as u32, |inner| {
      prop_oneof![
        (inner.clone(), any::<bool>()).prop_map(|(elem, readonly)| TypeRecipe::Array {
          elem: Box::new(elem),
          readonly,
        }),
        prop::collection::vec(inner.clone(), 0..=MAX_BREADTH)
          .prop_map(|elems| TypeRecipe::Tuple { elems }),
        prop::collection::vec(inner.clone(), 1..=MAX_BREADTH)
          .prop_map(|members| TypeRecipe::Union { members }),
        prop::collection::vec(inner.clone(), 1..=MAX_BREADTH)
          .prop_map(|members| TypeRecipe::Intersection { members }),
        prop::collection::vec(
          (
            prop::sample::select(PROP_NAMES.to_vec()),
            inner.clone(),
            any::<bool>(),
            any::<bool>(),
          ),
          0..=3
        )
        .prop_map(|props| TypeRecipe::Object {
          props: props
            .into_iter()
            .map(|(name, ty, optional, readonly)| ObjProp {
              name,
              ty,
              optional,
              readonly,
            })
            .collect(),
        }),
      ]
    })
    .boxed()
}

fn recipe_pair() -> impl Strategy<Value = (TypeRecipe, TypeRecipe)> {
  (type_recipe(), type_recipe())
}

fn recipe_triple() -> impl Strategy<Value = (TypeRecipe, TypeRecipe, TypeRecipe)> {
  (type_recipe(), type_recipe(), type_recipe())
}

fn recipe_set(size: std::ops::RangeInclusive<usize>) -> impl Strategy<Value = Vec<TypeRecipe>> {
  prop::collection::vec(type_recipe(), size)
}

// ---------------------------------------------------------------------------
// 1. Canonicalization idempotence
// Law: wiki/crates/types-ts-interned.md § "TypeStore: interning and identity"
//      (canonicalize before interning; equal-up-to-ACI share one TypeId)
// ---------------------------------------------------------------------------
proptest! {
  #![proptest_config(ProptestConfig::with_cases(256))]

  #[test]
  fn canon_idempotent(recipe in type_recipe()) {
    let store = TypeStore::new();
    let t = materialize(&store, &recipe);
    let once = store.canon(t);
    let twice = store.canon(once);
    // canon(canon(t)) == canon(t)
    prop_assert_eq!(once, twice);
  }
}

// ---------------------------------------------------------------------------
// 2. Union ACI laws
// Law: wiki/crates/types-ts-interned.md § TypeStore — flatten/sort/dedup +
//      identities `T | never = T`; commutativity via sorted canonical members.
//      Also wiki/architecture/determinism.md (A | B and B | A → same ID).
// ---------------------------------------------------------------------------
proptest! {
  #![proptest_config(ProptestConfig::with_cases(256))]

  #[test]
  fn union_commutative(recipe in recipe_pair()) {
    let (a_r, b_r) = recipe;
    let store = TypeStore::new();
    let a = materialize(&store, &a_r);
    let b = materialize(&store, &b_r);
    prop_assert_eq!(store.union(vec![a, b]), store.union(vec![b, a]));
  }

  #[test]
  fn union_idempotent_singleton(recipe in type_recipe()) {
    let store = TypeStore::new();
    let a = materialize(&store, &recipe);
    // union([a, a]) collapses to the canonical singleton of a
    prop_assert_eq!(store.union(vec![a, a]), store.canon(a));
  }

  #[test]
  fn union_never_identity(recipe in type_recipe()) {
    let store = TypeStore::new();
    let a = materialize(&store, &recipe);
    let never = store.primitive_ids().never;
    // T | never = T  (wiki: types-ts-interned.md TypeStore identities)
    prop_assert_eq!(store.union(vec![a, never]), store.canon(a));
    prop_assert_eq!(store.union(vec![never, a]), store.canon(a));
  }
}

// ---------------------------------------------------------------------------
// 3. Intersection dual laws
// Law: wiki/crates/types-ts-interned.md § TypeStore — `T & unknown = T`,
//      sorted/deduped members (commutativity + idempotence).
// ---------------------------------------------------------------------------
proptest! {
  #![proptest_config(ProptestConfig::with_cases(256))]

  #[test]
  fn intersection_commutative(recipe in recipe_pair()) {
    let (a_r, b_r) = recipe;
    let store = TypeStore::new();
    let a = materialize(&store, &a_r);
    let b = materialize(&store, &b_r);
    prop_assert_eq!(
      store.intersection(vec![a, b]),
      store.intersection(vec![b, a])
    );
  }

  #[test]
  fn intersection_idempotent_singleton(recipe in type_recipe()) {
    let store = TypeStore::new();
    let a = materialize(&store, &recipe);
    prop_assert_eq!(store.intersection(vec![a, a]), store.canon(a));
  }

  #[test]
  fn intersection_unknown_identity(recipe in type_recipe()) {
    let store = TypeStore::new();
    let a = materialize(&store, &recipe);
    let unknown = store.primitive_ids().unknown;
    // T & unknown = T  (wiki: types-ts-interned.md TypeStore identities)
    prop_assert_eq!(store.intersection(vec![a, unknown]), store.canon(a));
    prop_assert_eq!(store.intersection(vec![unknown, a]), store.canon(a));
  }
}

// ---------------------------------------------------------------------------
// 4. type_cmp total-order laws
// Law: wiki/crates/types-ts-interned.md § TypeStore — `type_cmp` is the total
//      order used to sort union/intersection members before interning.
// ---------------------------------------------------------------------------
proptest! {
  #![proptest_config(ProptestConfig::with_cases(128))]

  #[test]
  fn type_cmp_reflexive_and_consistent(recipes in recipe_set(1..=6)) {
    let store = TypeStore::new();
    let ids: Vec<TypeId> = recipes
      .iter()
      .map(|r| store.canon(materialize(&store, r)))
      .collect();

    for &a in &ids {
      // Reflexivity
      prop_assert_eq!(store.type_cmp(a, a), Ordering::Equal);
    }

    for &a in &ids {
      for &b in &ids {
        let ord = store.type_cmp(a, b);
        // Consistency: Equal iff same TypeId after canon (inputs already canon)
        if ord == Ordering::Equal {
          prop_assert_eq!(a, b);
        } else {
          prop_assert_ne!(a, b);
        }
        // Equal iff same TypeId (biconditional)
        prop_assert_eq!(ord == Ordering::Equal, a == b);
      }
    }
  }

  #[test]
  fn type_cmp_antisymmetric(recipes in recipe_set(2..=6)) {
    let store = TypeStore::new();
    let ids: Vec<TypeId> = recipes
      .iter()
      .map(|r| store.canon(materialize(&store, r)))
      .collect();

    for &a in &ids {
      for &b in &ids {
        let ab = store.type_cmp(a, b);
        let ba = store.type_cmp(b, a);
        prop_assert_eq!(ab, ba.reverse());
        if ab == Ordering::Equal {
          prop_assert_eq!(a, b);
        }
      }
    }
  }

  #[test]
  fn type_cmp_transitive(recipes in recipe_set(3..=6)) {
    let store = TypeStore::new();
    let ids: Vec<TypeId> = recipes
      .iter()
      .map(|r| store.canon(materialize(&store, r)))
      .collect();

    for &a in &ids {
      for &b in &ids {
        for &c in &ids {
          let ab = store.type_cmp(a, b);
          let bc = store.type_cmp(b, c);
          let ac = store.type_cmp(a, c);
          // If a ≤ b and b ≤ c then a ≤ c
          if ab != Ordering::Greater && bc != Ordering::Greater {
            prop_assert_ne!(
              ac,
              Ordering::Greater,
              "transitivity failed: a={:?} b={:?} c={:?} ab={:?} bc={:?} ac={:?}",
              a,
              b,
              c,
              ab,
              bc,
              ac
            );
          }
        }
      }
    }
  }
}

// ---------------------------------------------------------------------------
// 5. Content-addressed determinism
// Law: wiki/crates/types-ts-interned.md § TypeStore — 128-bit fingerprints;
//      wiki/architecture/determinism.md — ID allocation independent of insertion
//      order / schedule; same construction → same TypeIds across stores.
// ---------------------------------------------------------------------------
proptest! {
  #![proptest_config(ProptestConfig::with_cases(128))]

  #[test]
  fn content_addressed_ids_match_across_fresh_stores(recipes in recipe_set(1..=8)) {
    let store_a = TypeStore::new();
    let store_b = TypeStore::new();
    for recipe in &recipes {
      let id_a = materialize(&store_a, recipe);
      let id_b = materialize(&store_b, recipe);
      prop_assert_eq!(
        id_a,
        id_b,
        "same recipe must yield the same TypeId in two fresh stores; recipe={:?}",
        recipe
      );
    }
  }

  #[test]
  fn content_addressed_sequence_replay(recipes in recipe_set(2..=8)) {
    // Record a construction sequence (recipe list) and replay on two stores.
    fn replay(store: &TypeStore, recipes: &[TypeRecipe]) -> Vec<TypeId> {
      recipes.iter().map(|r| materialize(store, r)).collect()
    }
    let ids_a = replay(&TypeStore::new(), &recipes);
    let ids_b = replay(&TypeStore::new(), &recipes);
    prop_assert_eq!(ids_a, ids_b);
  }
}

// ---------------------------------------------------------------------------
// 6. Relation stability under canonicalization
// Law: wiki/crates/types-ts-interned.md § Relation engine + TypeStore —
//      assignability is over canonical types; canon is a pure rewrite that must
//      not change relation verdicts.
// ---------------------------------------------------------------------------
proptest! {
  #![proptest_config(ProptestConfig::with_cases(128))]

  #[test]
  fn assignability_stable_under_canon(recipe in recipe_pair()) {
    let (a_r, b_r) = recipe;
    let store = TypeStore::new();
    let a = materialize(&store, &a_r);
    let b = materialize(&store, &b_r);
    let ca = store.canon(a);
    let cb = store.canon(b);

    // Default options/modes, no expander; bound steps for safety.
    let ctx = RelateCtx::new(Arc::clone(&store), store.options()).with_step_limit(50_000);
    let raw = ctx.is_assignable(a, b);
    let canonized = ctx.is_assignable(ca, cb);
    prop_assert_eq!(
      raw,
      canonized,
      "RelateCtx assignability must be invariant under canon; a={:?} b={:?} ca={:?} cb={:?}",
      a,
      b,
      ca,
      cb
    );
  }

  #[test]
  fn assignability_stable_under_canon_triples(recipe in recipe_triple()) {
    // Extra coverage: also check a ≔ a|never style rewrites stay relation-stable.
    let (a_r, b_r, c_r) = recipe;
    let store = TypeStore::new();
    let a = materialize(&store, &a_r);
    let b = materialize(&store, &b_r);
    let c = materialize(&store, &c_r);
    let never = store.primitive_ids().never;
    let a_with_never = store.union(vec![a, never]);
    let ctx = RelateCtx::new(Arc::clone(&store), store.options()).with_step_limit(50_000);
    prop_assert_eq!(
      ctx.is_assignable(a, b),
      ctx.is_assignable(store.canon(a_with_never), store.canon(b))
    );
    prop_assert_eq!(
      ctx.is_assignable(b, c),
      ctx.is_assignable(store.canon(b), store.canon(c))
    );
  }
}
