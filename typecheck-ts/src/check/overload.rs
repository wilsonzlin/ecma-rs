use std::collections::{hash_map::Entry, HashMap, HashSet};
use std::sync::Arc;

use diagnostics::{Diagnostic, Span};
use types_ts_interned::{
  Param, ReasonNode, RelateCtx, RelateTypeExpander, Signature, SignatureId, TupleElem, TypeDisplay,
  TypeId, TypeKind, TypeParamId, TypeStore,
};

use super::infer::infer_type_arguments_for_call;
use super::instantiate::InstantiationCache;
use crate::codes;

const MAX_NOTES: usize = 5;

type SignatureShapeKey = (
  Vec<(TypeId, bool, bool)>,
  Vec<types_ts_interned::TypeParamDecl>,
  Option<TypeId>,
);

/// Argument type information used during overload resolution and inference.
#[derive(Clone, Copy, Debug)]
pub struct CallArgType {
  pub ty: TypeId,
  pub spread: bool,
}

impl CallArgType {
  pub fn new(ty: TypeId) -> Self {
    Self { ty, spread: false }
  }

  pub fn spread(ty: TypeId) -> Self {
    Self { ty, spread: true }
  }
}

/// Result of resolving a call expression against a callable type.
#[derive(Debug)]
pub struct CallResolution {
  /// Selected return type; `unknown` when resolution failed.
  pub return_type: TypeId,
  /// Selected signature after instantiation, if any.
  pub signature: Option<SignatureId>,
  /// Best candidate signature (after instantiation) to use for contextual typing
  /// even when overload resolution fails (no match / ambiguous).
  pub contextual_signature: Option<SignatureId>,
  /// Diagnostics produced during resolution (ambiguous or no match).
  pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Copy, Debug)]
enum OverloadKind {
  Call,
  Construct,
}

/// Collect all callable signatures from a type, expanding unions/intersections
/// and object call signatures.
pub fn callable_signatures(store: &TypeStore, ty: TypeId) -> Vec<SignatureId> {
  callable_signatures_with_expander(store, ty, None)
}

/// Collect all callable signatures from a type, expanding unions/intersections
/// and object call signatures.
pub fn callable_signatures_with_expander(
  store: &TypeStore,
  ty: TypeId,
  expander: Option<&dyn RelateTypeExpander>,
) -> Vec<SignatureId> {
  match store.type_kind(ty) {
    TypeKind::Union(members) => union_common_signatures(store, OverloadKind::Call, &members, expander),
    _ => {
      let mut collected = Vec::new();
      collect_signatures(store, ty, &mut collected, &mut HashSet::new(), expander);
      let mut by_shape: HashMap<SignatureShapeKey, Vec<SignatureId>> = HashMap::new();
      for sig_id in collected.into_iter() {
        let sig = store.signature(sig_id);
        by_shape
          .entry(signature_shape_key(&sig))
          .or_default()
          .push(sig_id);
      }

      let mut out = Vec::new();
      for sig_ids in by_shape.values() {
        let has_non_unknown = sig_ids.iter().any(|sig_id| {
          let sig = store.signature(*sig_id);
          !matches!(store.type_kind(sig.ret), TypeKind::Unknown | TypeKind::Any)
        });

        let mut by_ret: HashMap<TypeId, SignatureId> = HashMap::new();
        for sig_id in sig_ids.iter().copied() {
          let sig = store.signature(sig_id);
          if has_non_unknown
            && matches!(store.type_kind(sig.ret), TypeKind::Unknown | TypeKind::Any)
          {
            continue;
          }
          match by_ret.entry(sig.ret) {
            Entry::Vacant(entry) => {
              entry.insert(sig_id);
            }
            Entry::Occupied(mut entry) => {
              if sig_id < *entry.get() {
                entry.insert(sig_id);
              }
            }
          }
        }
        out.extend(by_ret.values().copied());
      }

      out.sort();
      out
    }
  }
}

/// Collect all construct signatures from a type, expanding unions/intersections
/// and object construct signatures.
pub fn construct_signatures(store: &TypeStore, ty: TypeId) -> Vec<SignatureId> {
  construct_signatures_with_expander(store, ty, None)
}

/// Collect all construct signatures from a type, expanding unions/intersections
/// and object construct signatures.
pub fn construct_signatures_with_expander(
  store: &TypeStore,
  ty: TypeId,
  expander: Option<&dyn RelateTypeExpander>,
) -> Vec<SignatureId> {
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      union_common_signatures(store, OverloadKind::Construct, &members, expander)
    }
    _ => {
      let mut collected = Vec::new();
      collect_construct_signatures(store, ty, &mut collected, &mut HashSet::new(), expander);
      let mut by_shape: HashMap<SignatureShapeKey, (SignatureId, bool)> = HashMap::new();
      for sig_id in collected.into_iter() {
        let sig = store.signature(sig_id);
        let key = signature_shape_key(&sig);
        let is_unknown = matches!(store.type_kind(sig.ret), TypeKind::Unknown | TypeKind::Any);
        match by_shape.entry(key) {
          Entry::Vacant(entry) => {
            entry.insert((sig_id, is_unknown));
          }
          Entry::Occupied(mut entry) => {
            let (existing, existing_unknown) = *entry.get();
            if existing_unknown && !is_unknown {
              entry.insert((sig_id, is_unknown));
            } else if existing_unknown == is_unknown && sig_id < existing {
              entry.insert((sig_id, is_unknown));
            }
          }
        }
      }
      let mut out: Vec<_> = by_shape.values().map(|(id, _)| *id).collect();
      out.sort();
      out
    }
  }
}

/// Expected argument type at the given index, applying rest element expansion
/// when needed. Returns `None` if the signature does not accept an argument at
/// this position.
pub fn expected_arg_type_at(store: &TypeStore, sig: &Signature, index: usize) -> Option<TypeId> {
  let arity = analyze_arity(store, sig);
  expected_arg_type(store, sig, &arity, index).map(|p| p.ty)
}

/// Whether the signature can accept the given number of call arguments,
/// accounting for optional and rest parameters.
pub fn signature_allows_arg_count(store: &TypeStore, sig: &Signature, arg_count: usize) -> bool {
  analyze_arity(store, sig).allows(arg_count)
}

#[derive(Clone, Debug)]
enum RestStyle {
  Array(TypeId),
  Tuple {
    elems: Vec<TupleElem>,
    rest: Option<TypeId>,
  },
  Plain(TypeId),
}

#[derive(Clone, Debug)]
struct RestInfo {
  start: usize,
  style: RestStyle,
}

#[derive(Clone, Debug)]
struct ArityInfo {
  min: usize,
  max: Option<usize>,
  rest: Option<RestInfo>,
  fixed_len: usize,
}

#[derive(Clone, Copy, Debug)]
struct CallArityInfo {
  min: usize,
  max: Option<usize>,
}

impl ArityInfo {
  fn allows(&self, args: usize) -> bool {
    if args < self.min {
      return false;
    }
    if let Some(max) = self.max {
      if args > max {
        return false;
      }
    }
    true
  }

  fn allows_call(&self, call: &CallArityInfo) -> bool {
    if call.min < self.min {
      return false;
    }
    match (self.max, call.max) {
      (Some(sig_max), Some(call_max)) => call_max <= sig_max,
      (Some(_), None) => false,
      (None, Some(_)) => true,
      (None, None) => true,
    }
  }
}

fn analyze_call_arity(
  store: &TypeStore,
  args: &[CallArgType],
  expander: Option<&dyn RelateTypeExpander>,
) -> CallArityInfo {
  fn combine(a: Option<usize>, b: Option<usize>) -> Option<usize> {
    match (a, b) {
      (Some(left), Some(right)) => left.checked_add(right),
      _ => None,
    }
  }

  fn spread_arity(
    store: &TypeStore,
    ty: TypeId,
    expander: Option<&dyn RelateTypeExpander>,
    seen: &mut HashSet<TypeId>,
  ) -> (usize, Option<usize>) {
    if !seen.insert(ty) {
      // Recursive tuple aliases are treated conservatively.
      return (0, None);
    }
    match store.type_kind(ty) {
      TypeKind::Tuple(elems) => {
        let mut min = 0usize;
        let mut max = Some(0usize);
        for elem in elems {
          if elem.rest {
            let (rest_min, rest_max) = spread_arity(store, elem.ty, expander, seen);
            min += rest_min;
            max = combine(max, rest_max);
          } else {
            if !elem.optional {
              min += 1;
            }
            if let Some(max) = max.as_mut() {
              *max += 1;
            }
          }
        }
        (min, max)
      }
      // Arrays and unknown spreads can contribute any number of arguments.
      TypeKind::Array { .. } | TypeKind::Any | TypeKind::Unknown => (0, None),
      TypeKind::Union(members) => {
        let mut min: Option<usize> = None;
        let mut max = Some(0usize);
        for member in members {
          let (member_min, member_max) = spread_arity(store, member, expander, seen);
          min = Some(match min {
            Some(existing) => existing.min(member_min),
            None => member_min,
          });
          match (max, member_max) {
            (Some(existing), Some(member_max)) => max = Some(existing.max(member_max)),
            _ => max = None,
          }
        }
        (min.unwrap_or(0), max)
      }
      TypeKind::Ref { def, args } => match expander.and_then(|e| e.expand_ref(store, def, &args)) {
        Some(expanded) => spread_arity(store, expanded, expander, seen),
        None => (0, None),
      },
      _ => (0, None),
    }
  }

  let mut min = 0usize;
  let mut max = Some(0usize);
  for arg in args {
    if !arg.spread {
      min += 1;
      if let Some(max) = max.as_mut() {
        *max += 1;
      }
      continue;
    }
    let (spread_min, spread_max) = spread_arity(store, arg.ty, expander, &mut HashSet::new());
    min += spread_min;
    max = combine(max, spread_max);
  }

  CallArityInfo { min, max }
}

#[derive(Debug, Clone)]
enum CandidateRejection {
  Arity {
    min: usize,
    max: Option<usize>,
    actual_min: usize,
    actual_max: Option<usize>,
  },
  Inference(Vec<String>),
  ArgumentType {
    index: usize,
    arg: TypeId,
    param: TypeId,
  },
  ThisType {
    expected: TypeId,
    actual: Option<TypeId>,
  },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct MatchScore {
  /// Count of parameter positions where the parameter type was wider than the
  /// argument type (`!param <= arg`). Smaller is better.
  widen: u32,
  /// Count of parameters typed as `any` / `unknown` (highly permissive).
  any_like: u32,
  /// Count of parameters still represented as unresolved type parameters after
  /// instantiation.
  type_param: u32,
  /// Count of arguments matched via a rest parameter.
  rest: u32,
}

impl MatchScore {
  fn worst() -> Self {
    Self {
      widen: u32::MAX,
      any_like: u32::MAX,
      type_param: u32::MAX,
      rest: u32::MAX,
    }
  }
}

#[derive(Debug, Clone)]
struct CandidateOutcome {
  order: usize,
  sig_id: SignatureId,
  instantiated_sig: Signature,
  instantiated_id: SignatureId,
  subtype: bool,
  match_score: MatchScore,
  unknown_inferred: usize,
  return_rank: usize,
  rejection: Option<CandidateRejection>,
}

/// Resolve a call against a callable type, performing overload selection, generic
/// inference, and signature instantiation.
pub fn resolve_overloads(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  instantiation: &InstantiationCache,
  callee: TypeId,
  args: &[CallArgType],
  const_args: Option<&[TypeId]>,
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> CallResolution {
  resolve_overload_set(
    OverloadKind::Call,
    store,
    relate,
    instantiation,
    callee,
    args,
    const_args,
    this_arg,
    contextual_return,
    span,
    expander,
  )
}

/// Resolve a `new` expression against a constructable type, performing overload
/// selection and generic inference over constructor signatures.
pub fn resolve_construct_overloads(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  instantiation: &InstantiationCache,
  callee: TypeId,
  args: &[CallArgType],
  const_args: Option<&[TypeId]>,
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> CallResolution {
  resolve_overload_set(
    OverloadKind::Construct,
    store,
    relate,
    instantiation,
    callee,
    args,
    const_args,
    this_arg,
    contextual_return,
    span,
    expander,
  )
}

fn resolve_overload_set(
  kind: OverloadKind,
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  instantiation: &InstantiationCache,
  callee: TypeId,
  args: &[CallArgType],
  const_args: Option<&[TypeId]>,
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> CallResolution {
  let primitives = store.primitive_ids();
  let callee_kind = store.type_kind(callee);
  if matches!(callee_kind, TypeKind::Any | TypeKind::Unknown) {
    return CallResolution {
      return_type: primitives.unknown,
      signature: None,
      contextual_signature: None,
      diagnostics: Vec::new(),
    };
  }

  let has_spread = args.iter().any(|arg| arg.spread);
  let const_args = if has_spread {
    None
  } else {
    const_args.filter(|const_args| const_args.len() == args.len())
  };

  let mut candidates = Vec::new();
  match callee_kind {
    TypeKind::Union(members) => {
      candidates = union_common_signatures(store.as_ref(), kind, &members, expander);
    }
    _ => {
      match kind {
        OverloadKind::Call => collect_signatures(
          store.as_ref(),
          callee,
          &mut candidates,
          &mut HashSet::new(),
          expander,
        ),
        OverloadKind::Construct => collect_construct_signatures(
          store.as_ref(),
          callee,
          &mut candidates,
          &mut HashSet::new(),
          expander,
        ),
      };
      let mut seen_sig = HashSet::new();
      candidates.retain(|sig| seen_sig.insert(*sig));
    }
  }
  reorder_candidates_by_literal_types(store.as_ref(), &mut candidates);

  if candidates.is_empty() {
    let message = match kind {
      OverloadKind::Call => "expression is not callable",
      OverloadKind::Construct => "expression is not constructable",
    };
    let diag = codes::NO_OVERLOAD.error(message, span).with_note(format!(
      "callee has type {}",
      TypeDisplay::new(store, callee)
    ));
    return CallResolution {
      return_type: primitives.unknown,
      signature: None,
      contextual_signature: None,
      diagnostics: vec![diag],
    };
  }

  let call_arity = analyze_call_arity(store.as_ref(), args, expander);
  let base_expanded_args = expand_call_args(store.as_ref(), args, expander);

  let mut outcomes = Vec::with_capacity(candidates.len());
  for (order, sig_id) in candidates.into_iter().enumerate() {
    let original_sig = store.signature(sig_id);
    let allow_const_args = const_args.is_some() && original_sig.type_params.iter().any(|tp| tp.const_);
    let mut outcome = CandidateOutcome {
      order,
      sig_id,
      instantiated_sig: original_sig,
      instantiated_id: sig_id,
      subtype: false,
      match_score: MatchScore::worst(),
      unknown_inferred: 0,
      return_rank: usize::MAX,
      rejection: None,
    };

    let arity = analyze_arity(store.as_ref(), &outcome.instantiated_sig);
    if !arity.allows_call(&call_arity) {
      outcome.rejection = Some(CandidateRejection::Arity {
        min: arity.min,
        max: arity.max,
        actual_min: call_arity.min,
        actual_max: call_arity.max,
      });
      outcomes.push(outcome);
      continue;
    }

    let expanded_args = &base_expanded_args;
    let inference = infer_type_arguments_for_call(
      store,
      relate,
      &outcome.instantiated_sig,
      expanded_args,
      const_args,
      contextual_return,
    );
    outcome.unknown_inferred = count_unknown(
      store.as_ref(),
      &inference.substitutions,
      primitives.any,
      primitives.unknown,
    );
    if !inference.diagnostics.is_empty() {
      outcome.rejection = Some(CandidateRejection::Inference(
        inference
          .diagnostics
          .into_iter()
          .map(|d| d.message)
          .collect(),
      ));
      outcomes.push(outcome);
      continue;
    }

    let instantiated_id = instantiation.instantiate_signature(
      store,
      sig_id,
      &outcome.instantiated_sig,
      &inference.substitutions,
    );
    let instantiated_sig = store.signature(instantiated_id);
    outcome.instantiated_sig = instantiated_sig;
    outcome.instantiated_id = instantiated_id;
    outcome.return_rank = return_rank(store.as_ref(), outcome.instantiated_sig.ret);

    let arity = analyze_arity(store.as_ref(), &outcome.instantiated_sig);
    if !arity.allows_call(&call_arity) {
      outcome.rejection = Some(CandidateRejection::Arity {
        min: arity.min,
        max: arity.max,
        actual_min: call_arity.min,
        actual_max: call_arity.max,
      });
      outcomes.push(outcome);
      continue;
    }

    if matches!(kind, OverloadKind::Call) {
      if let Some(expected_this) = outcome.instantiated_sig.this_param {
        // In TypeScript, a plain call expression uses a `this` context of `void`.
        // Only property accesses (e.g. `obj.method()`) have a meaningful receiver.
        let actual_this = this_arg.unwrap_or(primitives.void);
        if !relate.is_assignable(actual_this, expected_this) {
          outcome.rejection = Some(CandidateRejection::ThisType {
            expected: expected_this,
            actual: Some(actual_this),
          });
          outcomes.push(outcome);
          continue;
        }
      }
    }

    let (score, subtype, mismatch) = check_arguments(
      store.as_ref(),
      relate,
      &outcome.instantiated_sig,
      &arity,
      expanded_args,
      &call_arity,
      allow_const_args,
      const_args,
    );
    outcome.match_score = score;
    outcome.subtype = subtype;
    outcome.rejection = mismatch;
    outcomes.push(outcome);
  }

  let mut applicable: Vec<&CandidateOutcome> =
    outcomes.iter().filter(|c| c.rejection.is_none()).collect();

  if applicable.is_empty() {
    let diag = build_no_match_diagnostic(store.as_ref(), relate, span, &outcomes);
    let mut fallback = outcomes.clone();
    fallback.sort_by_key(|candidate| fallback_rank_key(candidate, false));
    let (ret, contextual_signature) = fallback
      .first()
      .map(|candidate| {
        (
          candidate.instantiated_sig.ret,
          Some(candidate.instantiated_id),
        )
      })
      .unwrap_or((primitives.unknown, None));
    return CallResolution {
      return_type: ret,
      signature: None,
      contextual_signature,
      diagnostics: vec![diag],
    };
  }

  // TypeScript's overload resolution does not use the *contextual return type* to
  // filter/choose overloads. In particular, a context like:
  //
  //   declare function pick(x: any): number;
  //   declare function pick(x: any): string;
  //   const chosen: string = pick(0);
  //
  // still resolves to the first overload (`number`) and reports TS2322 at the
  // assignment site. (The contextual type can still participate in generic
  // inference via `infer_type_arguments_for_call` above.)
  applicable.sort_by_key(|candidate| fallback_rank_key(candidate, false));

  let best = applicable[0];
  CallResolution {
    return_type: best.instantiated_sig.ret,
    signature: Some(best.instantiated_id),
    contextual_signature: Some(best.instantiated_id),
    diagnostics: Vec::new(),
  }
}

fn collect_signatures(
  store: &TypeStore,
  ty: TypeId,
  out: &mut Vec<SignatureId>,
  seen: &mut HashSet<TypeId>,
  expander: Option<&dyn RelateTypeExpander>,
) {
  if !seen.insert(ty) {
    return;
  }
  match store.type_kind(ty) {
    TypeKind::Callable { overloads } => out.extend(overloads),
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      out.extend(shape.call_signatures);
    }
    TypeKind::Union(members) | TypeKind::Intersection(members) => {
      for member in members {
        collect_signatures(store, member, out, seen, expander);
      }
    }
    TypeKind::Ref { def, args } => {
      if let Some(expander) = expander {
        if let Some(expanded) = expander.expand_ref(store, def, &args) {
          collect_signatures(store, expanded, out, seen, Some(expander));
        }
      }
    }
    _ => {}
  }
}

fn signature_shape_key(sig: &Signature) -> SignatureShapeKey {
  (
    sig
      .params
      .iter()
      .map(|p| (p.ty, p.optional, p.rest))
      .collect(),
    sig.type_params.clone(),
    sig.this_param,
  )
}

fn reorder_candidates_by_literal_types(store: &TypeStore, candidates: &mut Vec<SignatureId>) {
  let mut specialized = Vec::new();
  let mut other = Vec::new();
  for sig_id in candidates.drain(..) {
    let sig = store.signature(sig_id);
    if signature_contains_literal_types(store, &sig) {
      specialized.push(sig_id);
    } else {
      other.push(sig_id);
    }
  }
  specialized.extend(other);
  *candidates = specialized;
}

pub fn signature_contains_literal_types(store: &TypeStore, sig: &Signature) -> bool {
  sig
    .params
    .iter()
    .any(|param| type_contains_literal_type(store, param.ty))
}

fn type_contains_literal_type(store: &TypeStore, ty: TypeId) -> bool {
  fn inner(store: &TypeStore, ty: TypeId, seen: &mut HashSet<TypeId>, depth: usize) -> bool {
    if depth > 32 {
      return false;
    }
    let ty = store.canon(ty);
    if !seen.insert(ty) {
      return false;
    }
    match store.type_kind(ty) {
      TypeKind::StringLiteral(_)
      | TypeKind::NumberLiteral(_)
      | TypeKind::BooleanLiteral(_)
      | TypeKind::BigIntLiteral(_)
      | TypeKind::TemplateLiteral(_)
      | TypeKind::UniqueSymbol => true,
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .iter()
        .copied()
        .any(|member| inner(store, member, seen, depth + 1)),
      TypeKind::Array { ty, .. } => inner(store, ty, seen, depth + 1),
      TypeKind::Tuple(elems) => elems
        .iter()
        .any(|elem| inner(store, elem.ty, seen, depth + 1)),
      TypeKind::Object(obj) => {
        let shape = store.shape(store.object(obj).shape);
        shape
          .properties
          .iter()
          .any(|prop| inner(store, prop.data.ty, seen, depth + 1))
      }
      TypeKind::Ref { args, .. } => args
        .iter()
        .copied()
        .any(|arg| inner(store, arg, seen, depth + 1)),
      _ => false,
    }
  }

  inner(store, ty, &mut HashSet::new(), 0)
}

fn dedup_signatures_by_shape(store: &TypeStore, sigs: Vec<SignatureId>) -> Vec<SignatureId> {
  let mut by_shape: HashMap<SignatureShapeKey, (SignatureId, bool)> = HashMap::new();
  for sig_id in sigs.into_iter() {
    let sig = store.signature(sig_id);
    let key = signature_shape_key(&sig);
    let is_unknown = matches!(store.type_kind(sig.ret), TypeKind::Unknown | TypeKind::Any);
    match by_shape.entry(key) {
      Entry::Vacant(entry) => {
        entry.insert((sig_id, is_unknown));
      }
      Entry::Occupied(mut entry) => {
        let (existing, existing_unknown) = *entry.get();
        if existing_unknown && !is_unknown {
          entry.insert((sig_id, is_unknown));
        } else if existing_unknown == is_unknown && sig_id < existing {
          entry.insert((sig_id, is_unknown));
        }
      }
    }
  }
  let mut out: Vec<_> = by_shape.values().map(|(id, _)| *id).collect();
  out.sort();
  out
}

fn union_common_signatures(
  store: &TypeStore,
  kind: OverloadKind,
  members: &[TypeId],
  expander: Option<&dyn RelateTypeExpander>,
) -> Vec<SignatureId> {
  let mut member_sigs: Vec<Vec<SignatureId>> = Vec::with_capacity(members.len());
  for member in members.iter().copied() {
    let mut sigs = Vec::new();
    match kind {
      OverloadKind::Call => {
        collect_signatures(store, member, &mut sigs, &mut HashSet::new(), expander)
      }
      OverloadKind::Construct => {
        collect_construct_signatures(store, member, &mut sigs, &mut HashSet::new(), expander)
      }
    }
    if sigs.is_empty() {
      return Vec::new();
    }
    sigs.sort();
    sigs.dedup();
    member_sigs.push(dedup_signatures_by_shape(store, sigs));
  }

  let Some((first, rest)) = member_sigs.split_first() else {
    return Vec::new();
  };

  let mut combined = first.clone();
  for sigs in rest.iter() {
    combined = intersect_signature_sets(store, &combined, sigs);
    if combined.is_empty() {
      return Vec::new();
    }
  }
  combined.sort();
  combined.dedup();
  combined
}

fn intersect_signature_sets(
  store: &TypeStore,
  lhs: &[SignatureId],
  rhs: &[SignatureId],
) -> Vec<SignatureId> {
  #[derive(Clone)]
  struct SigInfo {
    sig: Signature,
    arity: ArityInfo,
  }

  let lhs_info: Vec<SigInfo> = lhs
    .iter()
    .map(|sig_id| {
      let sig = store.signature(*sig_id);
      let arity = analyze_arity(store, &sig);
      SigInfo { sig, arity }
    })
    .collect();
  let rhs_info: Vec<SigInfo> = rhs
    .iter()
    .map(|sig_id| {
      let sig = store.signature(*sig_id);
      let arity = analyze_arity(store, &sig);
      SigInfo { sig, arity }
    })
    .collect();

  let mut by_shape: HashMap<SignatureShapeKey, TypeId> = HashMap::new();
  let mut order: Vec<SignatureShapeKey> = Vec::new();

  for lhs in lhs_info.iter() {
    for rhs in rhs_info.iter() {
      let Some(sig) = intersect_signatures(store, &lhs.sig, &lhs.arity, &rhs.sig, &rhs.arity)
      else {
        continue;
      };
      let key = signature_shape_key(&sig);
      match by_shape.entry(key.clone()) {
        Entry::Vacant(entry) => {
          entry.insert(sig.ret);
          order.push(key);
        }
        Entry::Occupied(mut entry) => {
          let merged = store.union(vec![*entry.get(), sig.ret]);
          entry.insert(merged);
        }
      }
    }
  }

  let mut out = Vec::with_capacity(order.len());
  for key in order {
    let ret = *by_shape.get(&key).expect("key should exist");
    let (params, type_params, this_param) = key;
    out.push(
      store.intern_signature(Signature {
        params: params
          .into_iter()
          .map(|(ty, optional, rest)| Param {
            name: None,
            ty,
            optional,
            rest,
          })
          .collect(),
        ret,
        type_params,
        this_param,
      }),
    );
  }

  out.sort();
  out.dedup();
  out
}

fn intersect_signatures(
  store: &TypeStore,
  lhs: &Signature,
  lhs_arity: &ArityInfo,
  rhs: &Signature,
  rhs_arity: &ArityInfo,
) -> Option<Signature> {
  if lhs.type_params != rhs.type_params {
    return None;
  }

  let min = lhs_arity.min.max(rhs_arity.min);
  let max = match (lhs_arity.max, rhs_arity.max) {
    (Some(a), Some(b)) => Some(a.min(b)),
    (Some(a), None) => Some(a),
    (None, Some(b)) => Some(b),
    (None, None) => None,
  };
  if let Some(max) = max {
    if min > max {
      return None;
    }
  }

  let this_param = match (lhs.this_param, rhs.this_param) {
    (Some(a), Some(b)) => {
      let combined = store.intersection(vec![a, b]);
      if is_obviously_empty_intersection(store, combined) {
        return None;
      }
      Some(combined)
    }
    (Some(a), None) => Some(a),
    (None, Some(b)) => Some(b),
    (None, None) => None,
  };

  let ret = store.union(vec![lhs.ret, rhs.ret]);

  let mut params = Vec::new();
  match max {
    Some(max) => {
      for idx in 0..max {
        let lhs = expected_arg_type(store, lhs, lhs_arity, idx)?;
        let rhs = expected_arg_type(store, rhs, rhs_arity, idx)?;
        let combined = store.intersection(vec![lhs.ty, rhs.ty]);
        if is_obviously_empty_intersection(store, combined) {
          return None;
        }
        params.push(Param {
          name: None,
          ty: combined,
          optional: idx >= min,
          rest: false,
        });
      }
    }
    None => {
      for idx in 0..min {
        let lhs = expected_arg_type(store, lhs, lhs_arity, idx)?;
        let rhs = expected_arg_type(store, rhs, rhs_arity, idx)?;
        let combined = store.intersection(vec![lhs.ty, rhs.ty]);
        if is_obviously_empty_intersection(store, combined) {
          return None;
        }
        params.push(Param {
          name: None,
          ty: combined,
          optional: false,
          rest: false,
        });
      }

      let lhs_rest = expected_arg_type(store, lhs, lhs_arity, min)?;
      let rhs_rest = expected_arg_type(store, rhs, rhs_arity, min)?;
      let combined = store.intersection(vec![lhs_rest.ty, rhs_rest.ty]);
      if is_obviously_empty_intersection(store, combined) {
        return None;
      }
      params.push(Param {
        name: None,
        ty: combined,
        optional: false,
        rest: true,
      });
    }
  }

  Some(Signature {
    params,
    ret,
    type_params: lhs.type_params.clone(),
    this_param,
  })
}

fn is_obviously_empty_intersection(store: &TypeStore, ty: TypeId) -> bool {
  let prim = store.primitive_ids();
  if ty == prim.never {
    return true;
  }
  let TypeKind::Intersection(members) = store.type_kind(ty) else {
    return false;
  };

  const STRING: u16 = 1 << 0;
  const NUMBER: u16 = 1 << 1;
  const BOOLEAN: u16 = 1 << 2;
  const BIGINT: u16 = 1 << 3;
  const SYMBOL: u16 = 1 << 4;
  const NULLISH: u16 = 1 << 5;
  const ALL: u16 = STRING | NUMBER | BOOLEAN | BIGINT | SYMBOL | NULLISH;

  fn primitive_mask(store: &TypeStore, ty: TypeId) -> Option<u16> {
    match store.type_kind(ty) {
      TypeKind::String | TypeKind::StringLiteral(_) | TypeKind::TemplateLiteral(_) => Some(STRING),
      TypeKind::Number | TypeKind::NumberLiteral(_) => Some(NUMBER),
      TypeKind::Boolean | TypeKind::BooleanLiteral(_) => Some(BOOLEAN),
      TypeKind::BigInt | TypeKind::BigIntLiteral(_) => Some(BIGINT),
      TypeKind::Symbol | TypeKind::UniqueSymbol => Some(SYMBOL),
      TypeKind::Null | TypeKind::Undefined | TypeKind::Void => Some(NULLISH),
      TypeKind::Union(members) => {
        let mut mask = 0u16;
        for member in members {
          mask |= primitive_mask(store, member)?;
        }
        Some(mask)
      }
      _ => None,
    }
  }

  let mut mask = ALL;
  let mut string_lit = None;
  let mut number_lit = None;
  let mut boolean_lit = None;
  let mut bigint_lit = None;
  let mut unique_symbol = false;

  for member in members {
    match store.type_kind(member) {
      TypeKind::StringLiteral(id) => {
        if let Some(existing) = string_lit {
          if existing != id {
            return true;
          }
        } else {
          string_lit = Some(id);
        }
      }
      TypeKind::NumberLiteral(num) => {
        if let Some(existing) = number_lit {
          if existing != num {
            return true;
          }
        } else {
          number_lit = Some(num);
        }
      }
      TypeKind::BooleanLiteral(value) => {
        if let Some(existing) = boolean_lit {
          if existing != value {
            return true;
          }
        } else {
          boolean_lit = Some(value);
        }
      }
      TypeKind::BigIntLiteral(value) => {
        if let Some(existing) = bigint_lit.as_ref() {
          if existing != &value {
            return true;
          }
        } else {
          bigint_lit = Some(value);
        }
      }
      TypeKind::UniqueSymbol => {
        if unique_symbol {
          // Two distinct unique symbols cannot overlap, but we do not track
          // identity here; treat it as potentially non-empty.
          return false;
        }
        unique_symbol = true;
      }
      _ => {}
    }

    let Some(member_mask) = primitive_mask(store, member) else {
      return false;
    };
    mask &= member_mask;
    if mask == 0 {
      return true;
    }
  }

  false
}

fn rank_key_no_id(
  candidate: &CandidateOutcome,
  contextual_applied: bool,
) -> (u8, MatchScore, usize, usize, usize) {
  let return_rank = if contextual_applied {
    candidate.return_rank
  } else {
    0
  };
  (
    if candidate.subtype { 0 } else { 1 },
    candidate.match_score,
    candidate.unknown_inferred,
    return_rank,
    candidate.instantiated_sig.params.len(),
  )
}

fn fallback_rank_key(
  candidate: &CandidateOutcome,
  contextual_applied: bool,
) -> (u8, MatchScore, usize, usize, usize, usize) {
  let (subtype, score, unknown_inferred, return_rank, params_len) =
    rank_key_no_id(candidate, contextual_applied);
  (
    subtype,
    score,
    unknown_inferred,
    return_rank,
    params_len,
    candidate.order,
  )
}

fn collect_construct_signatures(
  store: &TypeStore,
  ty: TypeId,
  out: &mut Vec<SignatureId>,
  seen: &mut HashSet<TypeId>,
  expander: Option<&dyn RelateTypeExpander>,
) {
  if !seen.insert(ty) {
    return;
  }
  match store.type_kind(ty) {
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      out.extend(shape.construct_signatures);
    }
    TypeKind::Union(members) | TypeKind::Intersection(members) => {
      for member in members {
        collect_construct_signatures(store, member, out, seen, expander);
      }
    }
    TypeKind::Ref { def, args } => {
      if let Some(expander) = expander {
        if let Some(expanded) = expander.expand_ref(store, def, &args) {
          collect_construct_signatures(store, expanded, out, seen, Some(expander));
        }
      }
    }
    _ => {}
  }
}

fn return_rank(store: &TypeStore, ty: TypeId) -> usize {
  match store.type_kind(ty) {
    TypeKind::Predicate { .. } => 0,
    TypeKind::Any | TypeKind::Unknown | TypeKind::Infer { .. } => 3,
    TypeKind::Boolean | TypeKind::BooleanLiteral(_) => 2,
    _ => 1,
  }
}

fn analyze_arity(store: &TypeStore, sig: &Signature) -> ArityInfo {
  let mut min = 0usize;
  let mut max: Option<usize> = Some(0);
  let mut rest = None;
  for (idx, param) in sig.params.iter().enumerate() {
    if param.rest {
      let style = rest_style(store, param);
      let (rest_min, rest_max) = rest_arity(&style);
      min += rest_min;
      max = combine_max(max, rest_max);
      rest = Some(RestInfo { start: idx, style });
      break;
    }
    if !param.optional {
      min += 1;
    }
    if let Some(existing) = max.as_mut() {
      *existing += 1;
    }
  }
  if rest.is_none() {
    if let Some(existing) = max.as_mut() {
      *existing = sig.params.len();
    }
  }
  let fixed_len = rest.as_ref().map(|r| r.start).unwrap_or(sig.params.len());
  ArityInfo {
    min,
    max,
    rest,
    fixed_len,
  }
}

fn rest_style(store: &TypeStore, param: &Param) -> RestStyle {
  match store.type_kind(param.ty) {
    TypeKind::Array { ty, .. } => RestStyle::Array(ty),
    TypeKind::Tuple(elems) => {
      let rest = elems
        .iter()
        .rev()
        .find(|e| e.rest)
        .map(|e| spread_element_type(store, e.ty));
      RestStyle::Tuple { elems, rest }
    }
    _ => RestStyle::Plain(param.ty),
  }
}

fn rest_arity(style: &RestStyle) -> (usize, Option<usize>) {
  match style {
    RestStyle::Array(_) | RestStyle::Plain(_) => (0, None),
    RestStyle::Tuple { elems, rest } => {
      let required = elems.iter().filter(|e| !e.optional && !e.rest).count();
      let max = if rest.is_some() {
        None
      } else {
        Some(elems.len())
      };
      (required, max)
    }
  }
}

fn combine_max(a: Option<usize>, b: Option<usize>) -> Option<usize> {
  match (a, b) {
    (Some(lhs), Some(rhs)) => lhs.checked_add(rhs),
    _ => None,
  }
}

fn spread_element_type(store: &TypeStore, ty: TypeId) -> TypeId {
  let prim = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Any => prim.any,
    TypeKind::Unknown => prim.unknown,
    TypeKind::Array { ty, .. } => ty,
    TypeKind::Tuple(elems) => {
      let mut out = Vec::new();
      for elem in elems {
        if elem.rest {
          out.push(spread_element_type(store, elem.ty));
        } else {
          out.push(elem.ty);
        }
      }
      if out.is_empty() {
        prim.unknown
      } else if out.len() == 1 {
        out[0]
      } else {
        store.union(out)
      }
    }
    TypeKind::Union(members) => {
      let elems: Vec<_> = members
        .into_iter()
        .map(|member| spread_element_type(store, member))
        .collect();
      store.union(elems)
    }
    TypeKind::Intersection(members) => {
      let elems: Vec<_> = members
        .into_iter()
        .map(|member| spread_element_type(store, member))
        .collect();
      store.intersection(elems)
    }
    _ => prim.unknown,
  }
}

#[derive(Clone, Copy)]
struct ExpectedParam {
  ty: TypeId,
  from_rest: bool,
  optional: bool,
}

fn expected_arg_type(
  store: &TypeStore,
  sig: &Signature,
  arity: &ArityInfo,
  index: usize,
) -> Option<ExpectedParam> {
  if index < arity.fixed_len {
    return sig.params.get(index).map(|p| ExpectedParam {
      ty: p.ty,
      from_rest: false,
      optional: p.optional,
    });
  }
  let rest = arity.rest.as_ref()?;
  let offset = index - rest.start;
  match &rest.style {
    RestStyle::Array(elem) => Some(ExpectedParam {
      ty: *elem,
      from_rest: true,
      optional: sig
        .params
        .get(rest.start)
        .map(|p| p.optional)
        .unwrap_or(false),
    }),
    RestStyle::Plain(ty) => Some(ExpectedParam {
      ty: *ty,
      from_rest: true,
      optional: sig
        .params
        .get(rest.start)
        .map(|p| p.optional)
        .unwrap_or(false),
    }),
    RestStyle::Tuple { elems, rest } => {
      if let Some(elem) = elems.get(offset) {
        Some(ExpectedParam {
          ty: if elem.rest {
            spread_element_type(store, elem.ty)
          } else {
            elem.ty
          },
          from_rest: true,
          optional: elem.optional,
        })
      } else {
        rest.map(|ty| ExpectedParam {
          ty,
          from_rest: true,
          optional: false,
        })
      }
    }
  }
}

fn check_arguments(
  store: &TypeStore,
  relate: &RelateCtx<'_>,
  sig: &Signature,
  arity: &ArityInfo,
  args: &[CallArgType],
  call_arity: &CallArityInfo,
  allow_const_args: bool,
  const_args: Option<&[TypeId]>,
) -> (MatchScore, bool, Option<CandidateRejection>) {
  let primitives = store.primitive_ids();
  let mut score = MatchScore {
    widen: 0,
    any_like: 0,
    type_param: 0,
    rest: 0,
  };
  let mut subtype = true;
  let allow_const_args = allow_const_args && const_args.is_some();
  for (idx, arg) in args.iter().enumerate() {
    let expected = match expected_arg_type(store, sig, arity, idx) {
      Some(param) => param,
      None => {
        return (
          MatchScore::worst(),
          false,
          Some(CandidateRejection::Arity {
            min: arity.min,
            max: arity.max,
            actual_min: call_arity.min,
            actual_max: call_arity.max,
          }),
        )
      }
    };
    if expected.from_rest {
      score.rest += 1;
    }
    match store.type_kind(expected.ty) {
      TypeKind::Any | TypeKind::Unknown => score.any_like += 1,
      TypeKind::TypeParam(_) | TypeKind::Infer { .. } => score.type_param += 1,
      _ => {}
    }

    let actual_ty = if arg.spread {
      relate.spread_element_type(arg.ty)
    } else {
      arg.ty
    };
    let expected_ty = if expected.optional {
      store.union(vec![expected.ty, primitives.undefined])
    } else {
      expected.ty
    };

    let arg_for_check = if !allow_const_args {
      actual_ty
    } else {
      let const_raw = const_args
        .and_then(|args| args.get(idx))
        .copied()
        .unwrap_or(arg.ty);
      let const_actual = if arg.spread {
        relate.spread_element_type(const_raw)
      } else {
        const_raw
      };
      if !relate.is_assignable(actual_ty, expected_ty) && relate.is_assignable(const_actual, expected_ty)
      {
        const_actual
      } else {
        actual_ty
      }
    };

    if !relate.is_assignable(arg_for_check, expected_ty) {
      return (
        score,
        false,
        Some(CandidateRejection::ArgumentType {
          index: idx,
          arg: actual_ty,
          param: expected_ty,
        }),
      );
    }

    if !relate.is_assignable(expected_ty, arg_for_check) {
      score.widen += 1;
    }

    if arg_for_check != expected_ty && !relate.is_strict_subtype(arg_for_check, expected_ty) {
      subtype = false;
    }
  }

  (score, subtype, None)
}

fn expand_call_args(
  store: &TypeStore,
  args: &[CallArgType],
  expander: Option<&dyn RelateTypeExpander>,
) -> Vec<CallArgType> {
  fn optional_type(store: &TypeStore, ty: TypeId, optional: bool) -> TypeId {
    if optional {
      store.union(vec![ty, store.primitive_ids().undefined])
    } else {
      ty
    }
  }

  fn expand_tuple(
    store: &TypeStore,
    ty: TypeId,
    expander: Option<&dyn RelateTypeExpander>,
    seen: &mut HashSet<TypeId>,
  ) -> Option<Vec<TupleElem>> {
    if !seen.insert(ty) {
      return None;
    }
    match store.type_kind(ty) {
      TypeKind::Tuple(elems) => Some(elems),
      TypeKind::Ref { def, args } => expander
        .and_then(|e| e.expand_ref(store, def, &args))
        .and_then(|expanded| expand_tuple(store, expanded, expander, seen)),
      _ => None,
    }
  }

  let mut out = Vec::new();
  for arg in args {
    if !arg.spread {
      out.push(*arg);
      continue;
    }

    if let Some(tuple) = expand_tuple(store, arg.ty, expander, &mut HashSet::new()) {
      for elem in tuple {
        if elem.rest {
          out.push(CallArgType {
            ty: elem.ty,
            spread: true,
          });
        } else {
          out.push(CallArgType {
            ty: optional_type(store, elem.ty, elem.optional),
            spread: false,
          });
        }
      }
      continue;
    }

    out.push(*arg);
  }
  out
}

fn count_unknown(
  store: &TypeStore,
  subst: &HashMap<TypeParamId, TypeId>,
  any: TypeId,
  unknown: TypeId,
) -> usize {
  subst
    .values()
    .filter(|v| {
      **v == any || **v == unknown || matches!(store.type_kind(**v), TypeKind::Infer { .. })
    })
    .count()
}

fn build_no_match_diagnostic(
  store: &TypeStore,
  relate: &RelateCtx<'_>,
  span: Span,
  outcomes: &[CandidateOutcome],
) -> Diagnostic {
  let mut diag = codes::NO_OVERLOAD.error("no overload matches this call", span);

  let mut rejected: Vec<&CandidateOutcome> = outcomes
    .iter()
    .filter(|outcome| outcome.rejection.is_some())
    .collect();
  rejected.sort_by_key(|candidate| fallback_rank_key(candidate, false));

  let width = rejected.len().max(1).to_string().len();
  let shown = rejected.len().min(MAX_NOTES);
  for (idx, outcome) in rejected.iter().take(shown).enumerate() {
    let Some(reason) = &outcome.rejection else {
      continue;
    };
    let sig = store.signature(outcome.sig_id);
    diag.push_note(format!(
      "overload {index:0width$}: {sig}: {reason}",
      index = idx + 1,
      width = width,
      sig = format_signature(store, &sig),
      reason = describe_rejection(store, relate, reason),
    ));
  }

  let hidden = rejected.len().saturating_sub(shown);
  if hidden > 0 {
    diag.push_note(format!("~ {hidden} overload(s) not shown"));
  }
  diag
}

fn first_reason_note(node: &ReasonNode) -> Option<String> {
  if node.outcome {
    return None;
  }
  if let Some(note) = &node.note {
    if note != "cached" {
      return Some(note.clone());
    }
  }
  for child in node.children.iter() {
    if let Some(note) = first_reason_note(child) {
      return Some(note);
    }
  }
  None
}

fn describe_rejection(
  store: &TypeStore,
  relate: &RelateCtx<'_>,
  reason: &CandidateRejection,
) -> String {
  match reason {
    CandidateRejection::Arity {
      min,
      max,
      actual_min,
      actual_max,
    } => match (max, actual_max) {
      (Some(max), Some(actual_max)) if min == max && actual_min == actual_max => {
        format!("expected {min} arguments but got {actual_min}")
      }
      (Some(max), Some(actual_max)) => format!(
        "expected between {min} and {max} arguments but got between {actual_min} and {actual_max}"
      ),
      (Some(max), None) => {
        format!("expected between {min} and {max} arguments but got at least {actual_min}")
      }
      (None, Some(actual_max)) => {
        format!("expected at least {min} arguments but got at most {actual_max}")
      }
      (None, None) => format!("expected at least {min} arguments but got at least {actual_min}"),
    },
    CandidateRejection::Inference(diags) => diags
      .first()
      .cloned()
      .unwrap_or_else(|| "type argument inference failed".to_string()),
    CandidateRejection::ArgumentType { index, arg, param } => {
      let mut msg = format!(
        "argument {} of type {} is not assignable to parameter of type {}",
        index + 1,
        TypeDisplay::new(store, *arg),
        TypeDisplay::new(store, *param)
      );
      let explanation = relate.explain_assignable(*arg, *param);
      if let Some(reason) = explanation.reason.as_ref() {
        if let Some(note) = first_reason_note(reason) {
          msg.push_str(&format!(" ({note})"));
        }
      }
      msg
    }
    CandidateRejection::ThisType { expected, actual } => match actual {
      Some(actual) => format!(
        "`this` of type {} is not assignable to expected type {}",
        TypeDisplay::new(store, *actual),
        TypeDisplay::new(store, *expected)
      ),
      None => format!(
        "call requires a `this` context of type {}",
        TypeDisplay::new(store, *expected)
      ),
    },
  }
}

fn format_signature(store: &TypeStore, sig: &Signature) -> String {
  let mut out = String::new();
  if !sig.type_params.is_empty() {
    out.push('<');
    for (idx, tp) in sig.type_params.iter().enumerate() {
      if idx > 0 {
        out.push_str(", ");
      }
      out.push_str(&format!("T{}", tp.id.0));
      if let Some(constraint) = tp.constraint {
        out.push_str(" extends ");
        out.push_str(&TypeDisplay::new(store, constraint).to_string());
      }
      if let Some(default) = tp.default {
        out.push_str(" = ");
        out.push_str(&TypeDisplay::new(store, default).to_string());
      }
    }
    out.push('>');
  }
  out.push('(');

  let mut wrote = false;
  if let Some(this_param) = sig.this_param {
    out.push_str("this: ");
    out.push_str(&TypeDisplay::new(store, this_param).to_string());
    wrote = true;
  }

  for param in sig.params.iter() {
    if wrote {
      out.push_str(", ");
    }
    if param.rest {
      out.push_str("...");
    }
    if let Some(name) = param.name {
      out.push_str(&store.name(name));
      if param.optional {
        out.push('?');
      }
      out.push_str(": ");
    }
    out.push_str(&TypeDisplay::new(store, param.ty).to_string());
    wrote = true;
  }

  out.push(')');
  out.push_str(" => ");
  out.push_str(&TypeDisplay::new(store, sig.ret).to_string());
  out
}
