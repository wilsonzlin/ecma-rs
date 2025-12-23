//! Minimal type representation with canonicalization and bounded relations.
//!
//! This crate is intentionally lightweight: it provides a small `Type` model,
//! a `canon` canonicalization routine that flattens/sorts/dedups unions and
//! intersections, and a cycle-safe `is_assignable` relation with explicit step
//! limits to guarantee termination on adversarial graphs.
//!
//! The guardrails here are exercised via property tests and fuzz entry points
//! to ensure we never panic and always produce deterministic canonical forms.

use ahash::{AHashMap, AHashSet};
use std::cmp::Ordering;

/// Maximum recursion depth used by canonicalization/relations to avoid stack
/// blow-ups on adversarial inputs.
const MAX_DEPTH: usize = 64;
/// Maximum number of relation steps before we conservatively give up.
const MAX_STEPS: usize = 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
  Never,
  Any,
  Unknown,
  Bool,
  Number,
  String,
  /// Named type or reference. In a fuller implementation this would be a
  /// DefId plus type arguments; here we just track an identifier.
  Ref(u32),
  Union(Vec<Type>),
  Intersection(Vec<Type>),
}

impl Type {
  /// Helper for constructing a canonical union/intersection with pre-sorted
  /// members. This is intentionally private; external callers should go
  /// through `canon` to ensure stability.
  fn new_union(mut members: Vec<Type>) -> Type {
    if members.is_empty() {
      return Type::Never;
    }
    stable_sort(&mut members);
    Type::Union(members)
  }

  fn new_intersection(mut members: Vec<Type>) -> Type {
    if members.is_empty() {
      return Type::Unknown;
    }
    stable_sort(&mut members);
    Type::Intersection(members)
  }
}

/// Canonicalize a type: flatten nested unions/intersections, sort members
/// deterministically, and remove duplicates/identity elements. The operation
/// is idempotent: `canon(canon(t)) == canon(t)`.
pub fn canon(ty: Type) -> Type {
  canon_inner(ty, 0)
}

fn canon_inner(ty: Type, depth: usize) -> Type {
  if depth > MAX_DEPTH {
    // Depth limit reached; return the type as-is to ensure termination.
    return ty;
  }

  match ty {
    Type::Union(members) => {
      let mut flat: Vec<Type> = Vec::new();
      for m in members {
        let m = canon_inner(m, depth + 1);
        match m {
          Type::Union(inner) => flat.extend(inner),
          Type::Never => {
            // Identity for union: ignore.
          }
          other => flat.push(other),
        }
      }
      dedup_and_sort(flat, true)
    }
    Type::Intersection(members) => {
      let mut flat: Vec<Type> = Vec::new();
      for m in members {
        let m = canon_inner(m, depth + 1);
        match m {
          Type::Intersection(inner) => flat.extend(inner),
          Type::Unknown => {
            // Identity for intersection: ignore.
          }
          other => flat.push(other),
        }
      }
      dedup_and_sort(flat, false)
    }
    other => other,
  }
}

fn dedup_and_sort(mut members: Vec<Type>, is_union: bool) -> Type {
  stable_sort(&mut members);
  let mut seen = AHashSet::new();
  members.retain(|m| seen.insert(m.clone()));

  // Collapse identities if everything was removed.
  if members.is_empty() {
    return if is_union { Type::Never } else { Type::Unknown };
  }

  if is_union {
    Type::new_union(members)
  } else {
    Type::new_intersection(members)
  }
}

fn stable_sort(types: &mut [Type]) {
  types.sort_by(|a, b| compare_types(a, b));
}

fn compare_types(a: &Type, b: &Type) -> Ordering {
  use Type::*;
  let rank = |t: &Type| match t {
    Never => 0,
    Any => 1,
    Unknown => 2,
    Bool => 3,
    Number => 4,
    String => 5,
    Ref(_) => 6,
    Union(_) => 7,
    Intersection(_) => 8,
  };

  let ra = rank(a);
  let rb = rank(b);
  if ra != rb {
    return ra.cmp(&rb);
  }

  match (a, b) {
    (Ref(a), Ref(b)) => a.cmp(b),
    (Union(a_mem), Union(b_mem)) | (Intersection(a_mem), Intersection(b_mem)) => {
      // Compare by length then lexicographically by debug string for
      // determinism without a deep structural order.
      let len_cmp = a_mem.len().cmp(&b_mem.len());
      if len_cmp != Ordering::Equal {
        len_cmp
      } else {
        format!("{:?}", a_mem).cmp(&format!("{:?}", b_mem))
      }
    }
    _ => Ordering::Equal,
  }
}

/// Simple, bounded assignability relation. This is intentionally conservative
/// and geared towards ensuring termination and determinism, not completeness of
/// TypeScript semantics.
pub fn is_assignable(src: &Type, dst: &Type) -> bool {
  let mut cache: AHashMap<(Type, Type), bool> = AHashMap::new();
  is_assignable_inner(src, dst, 0, &mut cache)
}

fn is_assignable_inner(
  src: &Type,
  dst: &Type,
  steps: usize,
  cache: &mut AHashMap<(Type, Type), bool>,
) -> bool {
  if steps > MAX_STEPS {
    // Too deep; bail out to guarantee termination.
    return false;
  }

  if let Some(&cached) = cache.get(&(src.clone(), dst.clone())) {
    return cached;
  }

  use Type::*;
  let result = match (src, dst) {
    // Basic identities.
    (Never, _) => true,
    (_, Any) => true,
    (Any, _) => true,
    (s, d) if s == d => true,
    // Unknown is top-ish: everything assignable to unknown, unknown only to itself/any.
    (_, Unknown) => true,
    (Unknown, d) => matches!(d, Unknown | Any),
    (Union(a), _) => a
      .iter()
      .all(|member| is_assignable_inner(member, dst, steps + 1, cache)),
    (_, Intersection(b)) => b
      .iter()
      .all(|member| is_assignable_inner(src, member, steps + 1, cache)),
    (Intersection(a), _) => a
      .iter()
      .any(|member| is_assignable_inner(member, dst, steps + 1, cache)),
    (_, Union(b)) => b
      .iter()
      .any(|member| is_assignable_inner(src, member, steps + 1, cache)),
    // Nominal-ish check for refs.
    (Ref(a), Ref(b)) => a == b,
    _ => false,
  };

  cache.insert((src.clone(), dst.clone()), result);
  result
}

/// Fuzzing entry point used by cargo-fuzz or external fuzzers. Compiled only
/// when the `fuzzing` feature is enabled.
#[cfg(feature = "fuzzing")]
pub fn fuzz_canon_and_assign(data: &[u8]) {
  let text = std::str::from_utf8(data).unwrap_or("");
  // Build a trivial Ref type from the hash of the input and exercise both
  // canon and is_assignable to ensure they never panic.
  let id = ahash::RandomState::with_seed(0).hash_one(text.as_bytes()) as u32;
  let ty = Type::Union(vec![Type::Ref(id), Type::Bool, Type::Ref(id)]);
  let canon_ty = canon(ty);
  let _ = is_assignable(&canon_ty, &Type::Any);
}
