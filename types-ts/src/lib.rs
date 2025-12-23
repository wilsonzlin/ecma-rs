//! Minimal type representation, canonicalization, and relation guardrails.
//!
//! This crate provides two complementary layers:
//! - A lightweight `Type` model with canonicalization (`canon`) and a bounded
//!   assignability relation (`is_assignable`) backed by property tests.
//! - A minimal `TypeStore`/`RelationEngine` pair used by the checker to
//!   exercise cycle-safe alias resolution and relations that never panic,
//!   instead returning conservative `Unknown` outcomes with optional notes.

use ahash::AHashMap;
use ahash::AHashSet;
use std::cmp::Ordering;
use std::collections::HashSet;

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

// === Type store / relation engine used by the checker ===

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(usize);

impl TypeId {
  pub fn raw(&self) -> usize {
    self.0
  }

  pub fn from_raw(raw: usize) -> Self {
    TypeId(raw)
  }
}

#[derive(Clone, Debug)]
pub enum TypeKind {
  Any,
  Never,
  Named(String),
  Union(Vec<TypeId>),
  Alias(TypeId),
}

#[derive(Debug, Default)]
pub struct TypeStore {
  types: Vec<TypeKind>,
}

impl TypeStore {
  pub fn new() -> Self {
    Self { types: Vec::new() }
  }

  pub fn intern(&mut self, kind: TypeKind) -> TypeId {
    let id = TypeId(self.types.len());
    self.types.push(kind);
    id
  }

  pub fn kind(&self, id: TypeId) -> &TypeKind {
    &self.types[id.0]
  }

  /// Resolves a chain of aliases, returning the final `TypeId` and an optional
  /// note when a cycle is detected. The function never panics and will stop at
  /// the first repeated type.
  pub fn resolve_alias(&self, mut id: TypeId) -> EvalResult {
    let mut visited = HashSet::new();
    let mut note = None;

    while let TypeKind::Alias(next) = self.kind(id).clone() {
      if !visited.insert(id) {
        note = Some(format!("alias cycle detected at type {:?}", id));
        break;
      }
      id = next;
    }

    EvalResult { resolved: id, note }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationOutcome {
  True,
  False,
  Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationResult {
  pub outcome: RelationOutcome,
  /// Optional note explaining why the conservative `Unknown` result was
  /// produced. This allows callers to surface an ICE note without panicking.
  pub ice_note: Option<String>,
}

pub struct RelationEngine<'a> {
  store: &'a TypeStore,
  visiting: HashSet<(TypeId, TypeId)>,
}

impl<'a> RelationEngine<'a> {
  pub fn new(store: &'a TypeStore) -> Self {
    Self {
      store,
      visiting: HashSet::new(),
    }
  }

  pub fn is_assignable(&mut self, source: TypeId, target: TypeId) -> RelationResult {
    self.relate(source, target)
  }

  fn relate(&mut self, source: TypeId, target: TypeId) -> RelationResult {
    if !self.visiting.insert((source, target)) {
      return RelationResult {
        outcome: RelationOutcome::Unknown,
        ice_note: Some(format!(
          "cycle detected while relating {:?} to {:?}",
          source, target
        )),
      };
    }

    let mut ice_note = None;
    let outcome = match (self.store.kind(source), self.store.kind(target)) {
      (TypeKind::Any, _) | (_, TypeKind::Any) => RelationOutcome::True,
      (TypeKind::Never, _) => RelationOutcome::True,
      (_, TypeKind::Never) => RelationOutcome::False,
      (TypeKind::Named(lhs), TypeKind::Named(rhs)) => {
        if lhs == rhs {
          RelationOutcome::True
        } else {
          RelationOutcome::False
        }
      }
      (TypeKind::Alias(inner), _) => {
        let nested = self.relate(*inner, target);
        ice_note = ice_note.or(nested.ice_note.clone());
        nested.outcome
      }
      (_, TypeKind::Alias(inner)) => {
        let nested = self.relate(source, *inner);
        ice_note = ice_note.or(nested.ice_note.clone());
        nested.outcome
      }
      (TypeKind::Union(members), _) => {
        let mut outcome = RelationOutcome::True;
        for member in members {
          let nested = self.relate(*member, target);
          ice_note = ice_note.or(nested.ice_note.clone());
          match nested.outcome {
            RelationOutcome::False => {
              outcome = RelationOutcome::False;
              break;
            }
            RelationOutcome::Unknown => outcome = RelationOutcome::Unknown,
            RelationOutcome::True => {}
          }
        }
        outcome
      }
      (_, TypeKind::Union(members)) => {
        let mut outcome = RelationOutcome::False;
        for member in members {
          let nested = self.relate(source, *member);
          ice_note = ice_note.or(nested.ice_note.clone());
          match nested.outcome {
            RelationOutcome::True => {
              outcome = RelationOutcome::True;
              break;
            }
            RelationOutcome::Unknown => outcome = RelationOutcome::Unknown,
            RelationOutcome::False => {}
          }
        }
        outcome
      }
    };

    self.visiting.remove(&(source, target));

    RelationResult { outcome, ice_note }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalResult {
  pub resolved: TypeId,
  pub note: Option<String>,
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn alias_cycles_do_not_panic() {
    let mut store = TypeStore::new();
    let first = store.intern(TypeKind::Alias(TypeId::from_raw(0)));
    // Force a cycle by pointing to self; the interned ID above is 0.
    let result = store.resolve_alias(first);
    assert_eq!(result.resolved, first);
    assert!(result.note.is_some());
  }

  #[test]
  fn relation_cycles_are_conservative() {
    let mut store = TypeStore::new();
    let a = store.intern(TypeKind::Named("A".to_string()));
    let b = store.intern(TypeKind::Alias(a));
    // Construct union that references itself to simulate a recursive shape.
    let recursive_union = store.intern(TypeKind::Union(vec![TypeId::from_raw(2)]));
    // Overwrite the union reference to point back to itself via aliasing.
    let _ = store.intern(TypeKind::Alias(recursive_union));

    let mut engine = RelationEngine::new(&store);
    let result = engine.is_assignable(recursive_union, b);
    assert_eq!(result.outcome, RelationOutcome::Unknown);
    assert!(result.ice_note.is_some());
  }
}
