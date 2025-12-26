use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use diagnostics::{Diagnostic, Span};
use types_ts_interned::{
  Param, RelateCtx, Signature, SignatureId, TupleElem, TypeDisplay, TypeId, TypeKind, TypeParamId,
  TypeStore,
};

use super::infer::{infer_type_arguments_for_call, TypeParamDecl};
use super::instantiate::Substituter;
use crate::codes;

const MAX_NOTES: usize = 5;

/// Result of resolving a call expression against a callable type.
#[derive(Debug)]
pub struct CallResolution {
  /// Selected return type; `unknown` when resolution failed.
  pub return_type: TypeId,
  /// Selected signature after instantiation, if any.
  pub signature: Option<SignatureId>,
  /// Diagnostics produced during resolution (ambiguous or no match).
  pub diagnostics: Vec<Diagnostic>,
}

/// Collect all callable signatures from a type, expanding unions/intersections
/// and object call signatures.
pub fn callable_signatures(store: &TypeStore, ty: TypeId) -> Vec<SignatureId> {
  let mut out = Vec::new();
  collect_signatures(store, ty, &mut out, &mut HashSet::new());
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

#[derive(Debug, Clone)]
struct CandidateOutcome {
  sig_id: SignatureId,
  display: String,
  instantiated_sig: Signature,
  instantiated_id: SignatureId,
  specificity: usize,
  unknown_inferred: usize,
  rejection: Option<CandidateRejection>,
}

/// Resolve a call against a callable type, performing overload selection, generic
/// inference, and signature instantiation.
pub fn resolve_overloads(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  callee: TypeId,
  args: &[TypeId],
  this_arg: Option<TypeId>,
  type_params: &[TypeParamDecl],
  contextual_return: Option<TypeId>,
  span: Span,
) -> CallResolution {
  let mut candidates = Vec::new();
  collect_signatures(store.as_ref(), callee, &mut candidates, &mut HashSet::new());
  let primitives = store.primitive_ids();
  if matches!(store.type_kind(callee), TypeKind::Any | TypeKind::Unknown) {
    return CallResolution {
      return_type: primitives.unknown,
      signature: None,
      diagnostics: Vec::new(),
    };
  }
  if candidates.is_empty() {
    let diag = codes::NO_OVERLOAD
      .error("expression is not callable", span)
      .with_note(format!(
        "callee has type {}",
        TypeDisplay::new(store, callee)
      ));
    return CallResolution {
      return_type: primitives.unknown,
      signature: None,
      diagnostics: vec![diag],
    };
  }

  let mut outcomes = Vec::new();

  for sig_id in candidates {
    let original_sig = store.signature(sig_id);
    let display = format_signature(store.as_ref(), &original_sig);
    let mut outcome = CandidateOutcome {
      sig_id,
      display,
      instantiated_sig: original_sig.clone(),
      instantiated_id: sig_id,
      specificity: usize::MAX,
      unknown_inferred: 0,
      rejection: None,
    };

    let arity = analyze_arity(store.as_ref(), &original_sig);
    if !arity.allows(args.len()) {
      outcome.rejection = Some(CandidateRejection::Arity {
        min: arity.min,
        max: arity.max,
        actual: args.len(),
      });
      outcomes.push(outcome);
      continue;
    }

    let inference =
      infer_type_arguments_for_call(store, &original_sig, type_params, args, contextual_return);
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

    let mut substituter = Substituter::new(Arc::clone(store), inference.substitutions.clone());
    let instantiated_id = substituter.substitute_signature(&original_sig);
    let instantiated_sig = store.signature(instantiated_id);

    let arity = analyze_arity(store.as_ref(), &instantiated_sig);
    if !arity.allows(args.len()) {
      outcome.rejection = Some(CandidateRejection::Arity {
        min: arity.min,
        max: arity.max,
        actual: args.len(),
      });
      outcomes.push(outcome);
      continue;
    }

    if let Some(expected_this) = instantiated_sig.this_param {
      match this_arg {
        Some(actual_this) => {
          if !relate.is_assignable(actual_this, expected_this) {
            outcome.rejection = Some(CandidateRejection::ThisType {
              expected: expected_this,
              actual: Some(actual_this),
            });
            outcomes.push(outcome);
            continue;
          }
        }
        None => {
          outcome.rejection = Some(CandidateRejection::ThisType {
            expected: expected_this,
            actual: None,
          });
          outcomes.push(outcome);
          continue;
        }
      }
    }

    let (_assignable, specificity, mismatch) =
      check_arguments(store.as_ref(), relate, &instantiated_sig, &arity, args);
    outcome.instantiated_sig = instantiated_sig;
    outcome.instantiated_id = instantiated_id;
    outcome.specificity = specificity;
    outcome.rejection = mismatch;
    outcomes.push(outcome);
    continue;
  }

  let mut applicable: Vec<&CandidateOutcome> =
    outcomes.iter().filter(|c| c.rejection.is_none()).collect();
  if applicable.is_empty() {
    let mut fallback = outcomes.clone();
    let diag = build_no_match_diagnostic(store.as_ref(), span, outcomes);
    fallback.sort_by(|a, b| {
      (
        a.specificity,
        a.unknown_inferred,
        a.instantiated_sig.params.len(),
        a.sig_id,
      )
        .cmp(&(
          b.specificity,
          b.unknown_inferred,
          b.instantiated_sig.params.len(),
          b.sig_id,
        ))
    });
    let ret = fallback
      .first()
      .map(|best| best.instantiated_sig.ret)
      .unwrap_or(primitives.unknown);
    return CallResolution {
      return_type: ret,
      signature: None,
      diagnostics: vec![diag],
    };
  }

  applicable.sort_by(|a, b| {
    (
      a.specificity,
      a.unknown_inferred,
      a.instantiated_sig.params.len(),
      a.sig_id,
    )
      .cmp(&(
        b.specificity,
        b.unknown_inferred,
        b.instantiated_sig.params.len(),
        b.sig_id,
      ))
  });

  let best = applicable[0];
  let best_score = (
    best.specificity,
    best.unknown_inferred,
    best.instantiated_sig.params.len(),
  );
  let tied: Vec<&CandidateOutcome> = applicable
    .into_iter()
    .take_while(|c| {
      (
        c.specificity,
        c.unknown_inferred,
        c.instantiated_sig.params.len(),
      ) == best_score
    })
    .collect();
  if tied.len() > 1 {
    let diag = build_ambiguous_diagnostic(span, &tied);
    return CallResolution {
      return_type: primitives.unknown,
      signature: None,
      diagnostics: vec![diag],
    };
  }

  CallResolution {
    return_type: best.instantiated_sig.ret,
    signature: Some(best.instantiated_id),
    diagnostics: Vec::new(),
  }
}

fn collect_signatures(
  store: &TypeStore,
  ty: TypeId,
  out: &mut Vec<SignatureId>,
  seen: &mut HashSet<TypeId>,
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
        collect_signatures(store, member, out, seen);
      }
    }
    _ => {}
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

fn check_arguments(
  store: &TypeStore,
  relate: &RelateCtx<'_>,
  sig: &Signature,
  arity: &ArityInfo,
  args: &[TypeId],
) -> (bool, usize, Option<CandidateRejection>) {
  let mut specificity = 0usize;
  for (idx, arg) in args.iter().enumerate() {
    let expected = match expected_arg_type(sig, arity, idx) {
      Some(param) => param,
      None => {
        return (
          false,
          specificity,
          Some(CandidateRejection::Arity {
            min: arity.min,
            max: arity.max,
            actual: args.len(),
          }),
        )
      }
    };
    if expected.from_rest {
      // Prefer fixed parameters over rest matches when both are applicable.
      specificity += 1;
    }
    if matches!(
      (store.type_kind(*arg), store.type_kind(expected.ty)),
      (TypeKind::Any | TypeKind::Unknown, _) | (_, TypeKind::Any | TypeKind::Unknown)
    ) {
      continue;
    }
    if !relate.is_assignable(*arg, expected.ty) {
      return (
        false,
        specificity,
        Some(CandidateRejection::ArgumentType {
          index: idx,
          arg: *arg,
          param: expected.ty,
        }),
      );
    }
    if !relate.is_assignable(expected.ty, *arg) {
      specificity += 1;
    }
    match store.type_kind(expected.ty) {
      TypeKind::Any | TypeKind::Unknown => {
        specificity += 2;
      }
      _ => {}
    }
  }
  (true, specificity, None)
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
  outcomes: Vec<CandidateOutcome>,
) -> Diagnostic {
  let mut diag = codes::NO_OVERLOAD.error("no overload matches this call", span);
  let mut shown = 0usize;
  for outcome in outcomes.iter() {
    if let Some(reason) = &outcome.rejection {
      if shown >= MAX_NOTES {
        break;
      }
      diag.push_note(format!(
        "{}: {}",
        outcome.display,
        describe_rejection(store, reason)
      ));
      shown += 1;
    }
  }
  let hidden = outcomes.len().saturating_sub(shown);
  if hidden > 0 {
    diag.push_note(format!("{hidden} overload(s) not shown"));
  }
  diag
}

fn build_ambiguous_diagnostic(span: Span, candidates: &[&CandidateOutcome]) -> Diagnostic {
  let mut diag = codes::AMBIGUOUS_OVERLOAD.error("call is ambiguous", span);
  let mut shown = 0usize;
  for candidate in candidates.iter() {
    if shown >= MAX_NOTES {
      break;
    }
    diag.push_note(candidate.display.clone());
    shown += 1;
  }
  let hidden = candidates.len().saturating_sub(shown);
  if hidden > 0 {
    diag.push_note(format!("{hidden} overload(s) not shown"));
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
      out.push_str(&format!("T{}", tp.0));
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
