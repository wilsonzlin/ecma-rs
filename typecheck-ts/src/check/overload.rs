use std::collections::{hash_map::Entry, HashMap, HashSet};
use std::sync::Arc;

use diagnostics::{Diagnostic, Span};
use types_ts_interned::{
  Param, RelateCtx, RelateTypeExpander, Signature, SignatureId, TupleElem, TypeDisplay, TypeId,
  TypeKind, TypeParamId, TypeStore,
};

use super::infer::infer_type_arguments_for_call;
use super::instantiate::InstantiationCache;
use crate::codes;

const MAX_NOTES: usize = 5;

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
  let mut collected = Vec::new();
  collect_signatures(store, ty, &mut collected, &mut HashSet::new(), None);
  let mut by_shape: HashMap<
    (
      Vec<(TypeId, bool, bool)>,
      Vec<types_ts_interned::TypeParamDecl>,
      Option<TypeId>,
    ),
    (SignatureId, bool),
  > = HashMap::new();
  for sig_id in collected.into_iter() {
    let sig = store.signature(sig_id);
    let key = (
      sig
        .params
        .iter()
        .map(|p| (p.ty, p.optional, p.rest))
        .collect::<Vec<_>>(),
      sig.type_params.clone(),
      sig.this_param,
    );
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

/// Expected argument type at the given index, applying rest element expansion
/// when needed. Returns `None` if the signature does not accept an argument at
/// this position.
pub fn expected_arg_type_at(store: &TypeStore, sig: &Signature, index: usize) -> Option<TypeId> {
  let arity = analyze_arity(store, sig);
  expected_arg_type(sig, &arity, index).map(|p| p.ty)
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
}

#[derive(Debug, Clone)]
enum CandidateRejection {
  Arity {
    min: usize,
    max: Option<usize>,
    actual: usize,
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
  sig_id: SignatureId,
  instantiated_sig: Signature,
  instantiated_id: SignatureId,
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
  args: &[TypeId],
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
  args: &[TypeId],
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
  args: &[TypeId],
  const_args: Option<&[TypeId]>,
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> CallResolution {
  let primitives = store.primitive_ids();
  if matches!(store.type_kind(callee), TypeKind::Any | TypeKind::Unknown) {
    return CallResolution {
      return_type: primitives.unknown,
      signature: None,
      contextual_signature: None,
      diagnostics: Vec::new(),
    };
  }

  let const_args = const_args.filter(|const_args| const_args.len() == args.len());

  let mut candidates = Vec::new();
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
  candidates.sort();

  if candidates.is_empty() {
    let message = match kind {
      OverloadKind::Call => "expression is not callable",
      OverloadKind::Construct => "expression is not constructable",
    };
    let diag = codes::NO_OVERLOAD
      .error(message, span)
      .with_note(format!(
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

  let mut outcomes = Vec::with_capacity(candidates.len());
  for sig_id in candidates {
    let original_sig = store.signature(sig_id);
    let mut outcome = CandidateOutcome {
      sig_id,
      instantiated_sig: original_sig,
      instantiated_id: sig_id,
      match_score: MatchScore::worst(),
      unknown_inferred: 0,
      return_rank: usize::MAX,
      rejection: None,
    };

    let arity = analyze_arity(store.as_ref(), &outcome.instantiated_sig);
    if !arity.allows(args.len()) {
      outcome.rejection = Some(CandidateRejection::Arity {
        min: arity.min,
        max: arity.max,
        actual: args.len(),
      });
      outcomes.push(outcome);
      continue;
    }

    let mut effective_args = None;
    if let Some(const_args) = const_args {
      for idx in 0..args.len() {
        if uses_const_arg(store.as_ref(), &outcome.instantiated_sig, &arity, idx) {
          if effective_args.is_none() {
            effective_args = Some(args.to_vec());
          }
          if let Some(slot) = effective_args.as_mut().and_then(|a| a.get_mut(idx)) {
            *slot = const_args[idx];
          }
        }
      }
    }
    let args = effective_args.as_deref().unwrap_or(args);

    let inference =
      infer_type_arguments_for_call(store, &outcome.instantiated_sig, args, contextual_return);
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
    if !arity.allows(args.len()) {
      outcome.rejection = Some(CandidateRejection::Arity {
        min: arity.min,
        max: arity.max,
        actual: args.len(),
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

    let (score, mismatch) =
      check_arguments(store.as_ref(), relate, &outcome.instantiated_sig, &arity, args);
    outcome.match_score = score;
    outcome.rejection = mismatch;
    outcomes.push(outcome);
  }

  let mut applicable: Vec<&CandidateOutcome> =
    outcomes.iter().filter(|c| c.rejection.is_none()).collect();

  if applicable.is_empty() {
    let diag = build_no_match_diagnostic(store.as_ref(), span, &outcomes);
    let mut fallback = outcomes.clone();
    fallback.sort_by_key(|candidate| fallback_rank_key(candidate, false));
    let (ret, contextual_signature) = fallback
      .first()
      .map(|candidate| (candidate.instantiated_sig.ret, Some(candidate.instantiated_id)))
      .unwrap_or((primitives.unknown, None));
    return CallResolution {
      return_type: ret,
      signature: None,
      contextual_signature,
      diagnostics: vec![diag],
    };
  }

  let mut contextual_applied = false;
  if let Some(expected_ret) = contextual_return {
    let contextual: Vec<&CandidateOutcome> = applicable
      .iter()
      .copied()
      .filter(|candidate| relate.is_assignable(candidate.instantiated_sig.ret, expected_ret))
      .collect();
    if !contextual.is_empty() {
      applicable = contextual;
      contextual_applied = true;
    }
  }

  applicable.sort_by_key(|candidate| fallback_rank_key(candidate, contextual_applied));

  let best_key_no_id = rank_key_no_id(applicable[0], contextual_applied);
  let best_candidates: Vec<&CandidateOutcome> = applicable
    .iter()
    .copied()
    .filter(|candidate| rank_key_no_id(candidate, contextual_applied) == best_key_no_id)
    .collect();

  if best_candidates.len() > 1 {
    let diag = build_ambiguous_diagnostic(store.as_ref(), span, &best_candidates);
    let mut ret_types: Vec<TypeId> = best_candidates
      .iter()
      .map(|candidate| candidate.instantiated_sig.ret)
      .collect();
    ret_types.sort();
    ret_types.dedup();
    let ret = if ret_types.is_empty() {
      primitives.unknown
    } else if ret_types.len() == 1 {
      ret_types[0]
    } else {
      store.union(ret_types)
    };
    let contextual_signature = best_candidates
      .iter()
      .min_by_key(|candidate| candidate.sig_id)
      .map(|candidate| candidate.instantiated_id);
    return CallResolution {
      return_type: ret,
      signature: None,
      contextual_signature,
      diagnostics: vec![diag],
    };
  }

  let best = best_candidates[0];
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

fn rank_key_no_id(
  candidate: &CandidateOutcome,
  contextual_applied: bool,
) -> (MatchScore, usize, usize, usize) {
  let return_rank = if contextual_applied {
    candidate.return_rank
  } else {
    0
  };
  (
    candidate.match_score,
    candidate.unknown_inferred,
    return_rank,
    candidate.instantiated_sig.params.len(),
  )
}

fn fallback_rank_key(
  candidate: &CandidateOutcome,
  contextual_applied: bool,
) -> (MatchScore, usize, usize, usize, SignatureId) {
  let (score, unknown_inferred, return_rank, params_len) =
    rank_key_no_id(candidate, contextual_applied);
  (score, unknown_inferred, return_rank, params_len, candidate.sig_id)
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
      let rest = elems.iter().rev().find(|e| e.rest).map(|e| e.ty);
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

#[derive(Clone, Copy)]
struct ExpectedParam {
  ty: TypeId,
  from_rest: bool,
}

fn expected_arg_type(sig: &Signature, arity: &ArityInfo, index: usize) -> Option<ExpectedParam> {
  if index < arity.fixed_len {
    return sig.params.get(index).map(|p| ExpectedParam {
      ty: p.ty,
      from_rest: false,
    });
  }
  let rest = arity.rest.as_ref()?;
  let offset = index - rest.start;
  match &rest.style {
    RestStyle::Array(elem) => Some(ExpectedParam {
      ty: *elem,
      from_rest: true,
    }),
    RestStyle::Plain(ty) => Some(ExpectedParam {
      ty: *ty,
      from_rest: true,
    }),
    RestStyle::Tuple { elems, rest } => {
      if let Some(elem) = elems.get(offset) {
        Some(ExpectedParam {
          ty: elem.ty,
          from_rest: true,
        })
      } else {
        rest.map(|ty| ExpectedParam {
          ty,
          from_rest: true,
        })
      }
    }
  }
}

fn uses_const_arg(store: &TypeStore, sig: &Signature, arity: &ArityInfo, index: usize) -> bool {
  let Some(expected) = expected_arg_type(sig, arity, index) else {
    return false;
  };
  let TypeKind::TypeParam(param_id) = store.type_kind(expected.ty) else {
    return false;
  };
  sig
    .type_params
    .iter()
    .any(|decl| decl.id == param_id && decl.const_)
}

fn check_arguments(
  store: &TypeStore,
  relate: &RelateCtx<'_>,
  sig: &Signature,
  arity: &ArityInfo,
  args: &[TypeId],
) -> (MatchScore, Option<CandidateRejection>) {
  let mut score = MatchScore {
    widen: 0,
    any_like: 0,
    type_param: 0,
    rest: 0,
  };

  for (idx, arg) in args.iter().enumerate() {
    let expected = match expected_arg_type(sig, arity, idx) {
      Some(param) => param,
      None => {
        return (
          MatchScore::worst(),
          Some(CandidateRejection::Arity {
            min: arity.min,
            max: arity.max,
            actual: args.len(),
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

    if !relate.is_assignable(*arg, expected.ty) {
      return (
        score,
        Some(CandidateRejection::ArgumentType {
          index: idx,
          arg: *arg,
          param: expected.ty,
        }),
      );
    }

    if !relate.is_assignable(expected.ty, *arg) {
      score.widen += 1;
    }
  }

  (score, None)
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
      reason = describe_rejection(store, reason),
    ));
  }

  let hidden = rejected.len().saturating_sub(shown);
  if hidden > 0 {
    diag.push_note(format!("~ {hidden} overload(s) not shown"));
  }
  diag
}

fn build_ambiguous_diagnostic(
  store: &TypeStore,
  span: Span,
  best_candidates: &[&CandidateOutcome],
) -> Diagnostic {
  let mut diag = codes::AMBIGUOUS_OVERLOAD.error("call is ambiguous", span);
  let mut candidates: Vec<&CandidateOutcome> = best_candidates.iter().copied().collect();
  candidates.sort_by_key(|candidate| candidate.sig_id);

  let width = candidates.len().max(1).to_string().len();
  let shown = candidates.len().min(MAX_NOTES);
  for (idx, outcome) in candidates.iter().take(shown).enumerate() {
    let sig = store.signature(outcome.sig_id);
    diag.push_note(format!(
      "overload {index:0width$}: {sig}",
      index = idx + 1,
      width = width,
      sig = format_signature(store, &sig),
    ));
  }

  let hidden = candidates.len().saturating_sub(shown);
  if hidden > 0 {
    diag.push_note(format!("~ {hidden} overload(s) not shown"));
  }
  diag
}

fn describe_rejection(store: &TypeStore, reason: &CandidateRejection) -> String {
  match reason {
    CandidateRejection::Arity { min, max, actual } => match max {
      Some(max) if min == max => format!("expected {min} arguments but got {actual}"),
      Some(max) => format!("expected between {min} and {max} arguments but got {actual}"),
      None => format!("expected at least {min} arguments but got {actual}"),
    },
    CandidateRejection::Inference(diags) => diags
      .first()
      .cloned()
      .unwrap_or_else(|| "type argument inference failed".to_string()),
    CandidateRejection::ArgumentType { index, arg, param } => format!(
      "argument {} of type {} is not assignable to parameter of type {}",
      index + 1,
      TypeDisplay::new(store, *arg),
      TypeDisplay::new(store, *param)
    ),
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
