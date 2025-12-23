use proptest::prelude::*;
use types_ts::canon;
use types_ts::is_assignable;
use types_ts::Type;

fn arb_leaf() -> impl Strategy<Value = Type> {
  prop_oneof![
    Just(Type::Never),
    Just(Type::Any),
    Just(Type::Unknown),
    Just(Type::Bool),
    Just(Type::Number),
    Just(Type::String),
    (0u32..16).prop_map(Type::Ref),
  ]
}

fn arb_type(depth: u32) -> impl Strategy<Value = Type> {
  let leaf = arb_leaf();
  leaf.prop_recursive(depth, 32, 6, |inner| {
    prop_oneof![
      prop::collection::vec(inner.clone(), 0..4).prop_map(Type::Union),
      prop::collection::vec(inner, 0..4).prop_map(Type::Intersection),
    ]
  })
}

proptest! {
  #[test]
  fn canon_is_idempotent(t in arb_type(4)) {
    let once = canon(t.clone());
    let twice = canon(once.clone());
    prop_assert_eq!(once, twice);
  }

  #[test]
fn union_order_is_stable(members in prop::collection::vec(arb_leaf(), 0..6)) {
  let ty = Type::Union(members);
  let canon_ty = canon(ty);
  if let Type::Union(sorted) = canon_ty {
      prop_assert!(is_canonically_sorted(&sorted));
  }
}

  #[test]
fn intersection_order_is_stable(members in prop::collection::vec(arb_leaf(), 0..6)) {
  let ty = Type::Intersection(members);
  let canon_ty = canon(ty);
  if let Type::Intersection(sorted) = canon_ty {
      prop_assert!(is_canonically_sorted(&sorted));
  }
}

  #[test]
fn assignable_terminates(a in arb_type(3), b in arb_type(3)) {
  let _ = is_assignable(&a, &b);
  // Success criterion is non-panicking termination; no assertion needed.
  }
}

fn type_rank(t: &Type) -> u8 {
  match t {
    Type::Never => 0,
    Type::Any => 1,
    Type::Unknown => 2,
    Type::Bool => 3,
    Type::Number => 4,
    Type::String => 5,
    Type::Ref(_) => 6,
    Type::Union(_) => 7,
    Type::Intersection(_) => 8,
  }
}

fn is_canonically_sorted(list: &[Type]) -> bool {
  list.windows(2).all(|w| {
    let (a, b) = (&w[0], &w[1]);
    let ra = type_rank(a);
    let rb = type_rank(b);
    if ra != rb {
      ra <= rb
    } else {
      match (a, b) {
        (Type::Ref(a_id), Type::Ref(b_id)) => a_id <= b_id,
        _ => format!("{:?}", a) <= format!("{:?}", b),
      }
    }
  })
}
