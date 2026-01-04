use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::instantiate::Substituter;
use super::overload::{expected_arg_type_at, CallArgType};
use types_ts_interned::{
  RelateCtx, Shape, Signature, TupleElem, TypeDisplay, TypeId, TypeKind, TypeParamDecl, TypeParamId,
  TypeStore,
};

/// Diagnostic emitted when inference fails to satisfy a constraint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferenceDiagnostic {
  pub param: TypeParamId,
  pub constraint: TypeId,
  pub actual: TypeId,
  pub message: String,
}

/// Result of attempting to infer type arguments for a signature.
#[derive(Clone, Debug, Default)]
pub struct InferenceResult {
  pub substitutions: HashMap<TypeParamId, TypeId>,
  pub diagnostics: Vec<InferenceDiagnostic>,
}

/// Infer type arguments for a call to a generic function signature.
///
/// Inference proceeds by relating the declared parameter types against the
/// provided argument types, collecting lower and upper bounds for each type
/// parameter depending on variance.
pub fn infer_type_arguments_for_call(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  sig: &Signature,
  args: &[CallArgType],
  const_args: Option<&[TypeId]>,
  contextual_return: Option<TypeId>,
) -> InferenceResult {
  let decls: HashMap<TypeParamId, TypeParamDecl> = sig
    .type_params
    .iter()
    .map(|decl| (decl.id, decl.clone()))
    .collect();

  let mut ctx = InferenceContext::new(Arc::clone(store), relate, decls);

  // Variadic tuple inference: `...args: T` where `T extends any[]`.
  let rest_index = sig.params.iter().position(|p| p.rest);
  let mut skip_from_index = None;
  if let Some(rest_index) = rest_index {
    match store.type_kind(sig.params[rest_index].ty) {
      TypeKind::TypeParam(tp) => {
        if ctx.decls.contains_key(&tp) {
          let rest_args = args.get(rest_index..).unwrap_or(&[]);
          let rest_const_args = const_args.and_then(|types| types.get(rest_index..));
          let readonly = ctx.decls.get(&tp).is_some_and(|decl| decl.const_);
          let inferred =
            infer_variadic_rest_tuple(store.as_ref(), rest_args, rest_const_args, readonly);
          ctx.add_bound(tp, Variance::Covariant, inferred);
          skip_from_index = Some(rest_index);
        }
      }
      TypeKind::Array { ty, .. } => {
        if let TypeKind::TypeParam(tp) = store.type_kind(ty) {
          if ctx.decls.contains_key(&tp) {
            let rest_args = args.get(rest_index..).unwrap_or(&[]);
            let rest_const_args = const_args.and_then(|types| types.get(rest_index..));
            let use_const = ctx.decls.get(&tp).is_some_and(|decl| decl.const_);
            let inferred = infer_homogenous_rest_array_element(
              store.as_ref(),
              relate,
              rest_args,
              rest_const_args,
              use_const,
            );
            ctx.add_bound(tp, Variance::Covariant, inferred);
            skip_from_index = Some(rest_index);
          }
        }
      }
      _ => {}
    }
  }

  for (idx, arg) in args.iter().enumerate() {
    if skip_from_index.is_some_and(|skip| idx >= skip) {
      break;
    }
    let Some(expected) = expected_arg_type_at(store.as_ref(), sig, idx) else {
      continue;
    };
    let regular = if arg.spread {
      relate.spread_element_type(arg.ty)
    } else {
      arg.ty
    };
    let const_ty = const_args
      .and_then(|types| types.get(idx))
      .copied()
      .unwrap_or(arg.ty);
    let const_ = if arg.spread {
      relate.spread_element_type(const_ty)
    } else {
      const_ty
    };
    ctx.constrain(expected, ArgPair { regular, const_ }, Variance::Covariant);
  }

  if let Some(ret) = contextual_return {
    ctx.constrain(
      sig.ret,
      ArgPair {
        regular: ret,
        const_: ret,
      },
      Variance::Covariant,
    );
  }

  let order: Vec<TypeParamId> = sig.type_params.iter().map(|tp| tp.id).collect();
  ctx.solve(&order)
}

fn infer_variadic_rest_tuple(
  store: &TypeStore,
  rest_args: &[CallArgType],
  const_args: Option<&[TypeId]>,
  readonly: bool,
) -> TypeId {
  if let [only] = rest_args {
    if only.spread {
      let only_ty = const_args.and_then(|args| args.first()).copied().unwrap_or(only.ty);
      match store.type_kind(only_ty) {
        // For `f<T extends any[]>(...args: T)` and `f(...arr)` where `arr` is a
        // non-tuple array, `tsc` infers `T` as the array type (not `[...T]`).
        TypeKind::Array { .. }
        // Tuple spreads are expanded by the caller (overload checker) when the
        // tuple type is known; but if a raw spread tuple arrives, preserve it.
        | TypeKind::Tuple(_) => return only_ty,
        _ => {}
      }
    }
  }

  let elems: Vec<TupleElem> = rest_args
    .iter()
    .enumerate()
    .map(|arg| TupleElem {
      ty: const_args
        .and_then(|args| args.get(arg.0))
        .copied()
        .unwrap_or(arg.1.ty),
      optional: false,
      rest: arg.1.spread,
      readonly,
    })
    .collect();
  store.intern_type(TypeKind::Tuple(elems))
}

fn infer_homogenous_rest_array_element(
  store: &TypeStore,
  relate: &RelateCtx<'_>,
  rest_args: &[CallArgType],
  const_args: Option<&[TypeId]>,
  use_const: bool,
) -> TypeId {
  let prim = store.primitive_ids();
  let mut candidates = Vec::new();
  for (idx, arg) in rest_args.iter().enumerate() {
    let mut ty = if use_const {
      const_args
        .and_then(|types| types.get(idx))
        .copied()
        .unwrap_or(arg.ty)
    } else {
      arg.ty
    };
    if arg.spread {
      ty = relate.spread_element_type(ty);
    }
    candidates.push(ty);
  }

  if candidates.is_empty() {
    return prim.unknown;
  }

  if candidates.len() > 1 {
    let has_specific = candidates
      .iter()
      .any(|ty| !matches!(store.type_kind(*ty), TypeKind::Unknown | TypeKind::Any));
    if has_specific {
      candidates.retain(|ty| !matches!(store.type_kind(*ty), TypeKind::Unknown | TypeKind::Any));
    }
  }

  // Prefer a candidate that all other arguments are assignable to (e.g. if one
  // argument is already a union supertype).
  for candidate in candidates.iter().copied() {
    if candidates
      .iter()
      .copied()
      .all(|other| relate.is_assignable(other, candidate))
    {
      return candidate;
    }
  }

  // When all candidates are literals of the same primitive kind, widen to the
  // primitive type (`collect(1, 2)` infers `number`, not `1`).
  if candidates
    .iter()
    .all(|ty| matches!(store.type_kind(*ty), TypeKind::NumberLiteral(_)))
  {
    return prim.number;
  }
  if candidates
    .iter()
    .all(|ty| matches!(store.type_kind(*ty), TypeKind::StringLiteral(_)))
  {
    return prim.string;
  }
  if candidates
    .iter()
    .all(|ty| matches!(store.type_kind(*ty), TypeKind::BooleanLiteral(_)))
  {
    return prim.boolean;
  }
  if candidates
    .iter()
    .all(|ty| matches!(store.type_kind(*ty), TypeKind::BigIntLiteral(_)))
  {
    return prim.bigint;
  }

  // Otherwise, keep the first inferred type and let argument checking surface
  // mismatches (mirrors `tsc` for `collect(1, "x")`).
  candidates[0]
}

/// Infer type arguments using a contextual function type (e.g. arrow function
/// assignment) paired with the actual inferred signature of the expression.
pub fn infer_type_arguments_from_contextual_signature(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  type_params: &[TypeParamDecl],
  contextual_sig: &Signature,
  actual_sig: &Signature,
) -> InferenceResult {
  let decls: HashMap<TypeParamId, TypeParamDecl> = type_params
    .iter()
    .map(|decl| (decl.id, decl.clone()))
    .collect();

  let mut ctx = InferenceContext::new(Arc::clone(store), relate, decls);
  ctx.constrain_signature(contextual_sig, actual_sig, Variance::Covariant);
  let order: Vec<TypeParamId> = type_params.iter().map(|tp| tp.id).collect();
  ctx.solve(&order)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Variance {
  Covariant,
  Contravariant,
}

impl Variance {
  fn flip(self) -> Self {
    match self {
      Variance::Covariant => Variance::Contravariant,
      Variance::Contravariant => Variance::Covariant,
    }
  }
}

#[derive(Clone, Debug, Default)]
struct Bounds {
  lower: Vec<TypeId>,
  upper: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug)]
struct ArgPair {
  regular: TypeId,
  const_: TypeId,
}

struct InferenceContext<'a, 'h> {
  store: Arc<TypeStore>,
  relate: &'a RelateCtx<'h>,
  bounds: HashMap<TypeParamId, Bounds>,
  decls: HashMap<TypeParamId, TypeParamDecl>,
}

impl<'a, 'h> InferenceContext<'a, 'h> {
  fn new(
    store: Arc<TypeStore>,
    relate: &'a RelateCtx<'h>,
    decls: HashMap<TypeParamId, TypeParamDecl>,
  ) -> Self {
    Self {
      store,
      relate,
      bounds: HashMap::new(),
      decls,
    }
  }

  fn constrain(&mut self, param_ty: TypeId, arg: ArgPair, variance: Variance) {
    if param_ty == arg.regular && param_ty == arg.const_ {
      return;
    }

    // Covariant inference distributes unions to gather candidates.
    if variance == Variance::Covariant {
      match (self.store.type_kind(arg.regular), self.store.type_kind(arg.const_)) {
        (TypeKind::Union(regular), TypeKind::Union(const_)) if regular.len() == const_.len() => {
          for (regular, const_) in regular.into_iter().zip(const_) {
            self.constrain(param_ty, ArgPair { regular, const_ }, variance);
          }
          return;
        }
        (TypeKind::Union(members), _) => {
          for member in members {
            self.constrain(
              param_ty,
              ArgPair {
                regular: member,
                const_: arg.const_,
              },
              variance,
            );
          }
          return;
        }
        (_, TypeKind::Union(members)) => {
          for member in members {
            self.constrain(
              param_ty,
              ArgPair {
                regular: arg.regular,
                const_: member,
              },
              variance,
            );
          }
          return;
        }
        _ => {}
      }
    }

    match self.store.type_kind(param_ty) {
      TypeKind::TypeParam(id) => {
        if let Some(decl) = self.decls.get(&id) {
          self.add_bound(id, variance, if decl.const_ { arg.const_ } else { arg.regular });
        }
      }
      TypeKind::Union(mut options) => {
        // When some union constituents participate in inference, avoid
        // inferring from "naked" type parameters that would otherwise match any
        // argument and swamp the candidates.
        let has_structured = options.iter().any(|opt| {
          !matches!(self.store.type_kind(*opt), TypeKind::TypeParam(_))
            && self.contains_inferable_type_param(*opt, &mut HashSet::new())
        });
        if has_structured {
          options.retain(|opt| !matches!(self.store.type_kind(*opt), TypeKind::TypeParam(_)));
        }
        for opt in options {
          self.constrain(opt, arg, variance);
        }
      }
      TypeKind::Intersection(options) => {
        for opt in options {
          self.constrain(opt, arg, variance);
        }
      }
      TypeKind::Array { ty, .. } => {
        match (
          self.store.type_kind(arg.regular),
          self.store.type_kind(arg.const_),
        ) {
          (TypeKind::Array { ty: regular, .. }, TypeKind::Array { ty: const_, .. }) => {
            self.constrain(ty, ArgPair { regular, const_ }, variance);
          }
          (TypeKind::Array { ty: regular, .. }, TypeKind::Tuple(const_elems)) => {
            for elem in const_elems {
              let const_ = if elem.rest {
                self.relate.spread_element_type(elem.ty)
              } else {
                elem.ty
              };
              self.constrain(ty, ArgPair { regular, const_ }, variance);
            }
          }
          (TypeKind::Tuple(regular_elems), TypeKind::Array { ty: const_, .. }) => {
            for elem in regular_elems {
              let regular = if elem.rest {
                self.relate.spread_element_type(elem.ty)
              } else {
                elem.ty
              };
              self.constrain(ty, ArgPair { regular, const_ }, variance);
            }
          }
          (TypeKind::Tuple(regular_elems), TypeKind::Tuple(const_elems)) => {
            let prim = self.store.primitive_ids();
            let len = std::cmp::max(regular_elems.len(), const_elems.len());
            for idx in 0..len {
              let regular = regular_elems
                .get(idx)
                .or_else(|| regular_elems.last())
                .map(|e| {
                  if e.rest {
                    self.relate.spread_element_type(e.ty)
                  } else {
                    e.ty
                  }
                })
                .unwrap_or(prim.unknown);
              let const_ = const_elems
                .get(idx)
                .or_else(|| const_elems.last())
                .map(|e| {
                  if e.rest {
                    self.relate.spread_element_type(e.ty)
                  } else {
                    e.ty
                  }
                })
                .unwrap_or(regular);
              self.constrain(ty, ArgPair { regular, const_ }, variance);
            }
          }
          _ => {}
        }
      },
      TypeKind::Tuple(param_elems) => {
        let prim = self.store.primitive_ids();
        let regular_tuple = match self.store.type_kind(arg.regular) {
          TypeKind::Tuple(elems) => Some(elems),
          _ => None,
        };
        let const_tuple = match self.store.type_kind(arg.const_) {
          TypeKind::Tuple(elems) => Some(elems),
          _ => None,
        };

        let arg_len = std::cmp::max(
          regular_tuple.as_ref().map(|e| e.len()).unwrap_or(0),
          const_tuple.as_ref().map(|e| e.len()).unwrap_or(0),
        );
        if arg_len == 0 {
          return;
        }

        let tuple_elem_ty = |elem: &TupleElem| {
          if elem.rest {
            self.relate.spread_element_type(elem.ty)
          } else {
            elem.ty
          }
        };

        let mut arg_index = 0usize;
        for param_elem in param_elems {
          if param_elem.rest {
            let expected_elem_ty = self.relate.spread_element_type(param_elem.ty);
            while arg_index < arg_len {
              let regular = regular_tuple
                .as_ref()
                .and_then(|elems| elems.get(arg_index))
                .map(|elem| tuple_elem_ty(elem))
                .or_else(|| {
                  const_tuple
                    .as_ref()
                    .and_then(|elems| elems.get(arg_index))
                    .map(|elem| tuple_elem_ty(elem))
                })
                .unwrap_or(prim.unknown);
              let const_ = const_tuple
                .as_ref()
                .and_then(|elems| elems.get(arg_index))
                .map(|elem| tuple_elem_ty(elem))
                .unwrap_or(regular);
              self.constrain(expected_elem_ty, ArgPair { regular, const_ }, variance);
              arg_index += 1;
            }
            break;
          }
          if arg_index >= arg_len {
            break;
          }
          let regular = regular_tuple
            .as_ref()
            .and_then(|elems| elems.get(arg_index))
            .map(|elem| tuple_elem_ty(elem))
            .or_else(|| {
              const_tuple
                .as_ref()
                .and_then(|elems| elems.get(arg_index))
                .map(|elem| tuple_elem_ty(elem))
            })
            .unwrap_or(prim.unknown);
          let const_ = const_tuple
            .as_ref()
            .and_then(|elems| elems.get(arg_index))
            .map(|elem| tuple_elem_ty(elem))
            .unwrap_or(regular);
          self.constrain(param_elem.ty, ArgPair { regular, const_ }, variance);
          arg_index += 1;
        }
      }
      TypeKind::Callable { overloads } => {
        if let TypeKind::Callable {
          overloads: arg_overloads,
        } = self.store.type_kind(arg.regular)
        {
          if let (Some(param_sig), Some(arg_sig)) = (overloads.first(), arg_overloads.first()) {
            let param_sig = self.store.signature(*param_sig);
            let arg_sig = self.store.signature(*arg_sig);
            self.constrain_signature(&param_sig, &arg_sig, variance);
          }
        }
      }
      TypeKind::Ref { def, args } => {
        let TypeKind::Ref {
          def: arg_def,
          args: arg_args,
        } = self.store.type_kind(arg.regular)
        else {
          return;
        };
        if def != arg_def {
          return;
        }

        let const_args = match self.store.type_kind(arg.const_) {
          TypeKind::Ref { def: const_def, args } if const_def == def && args.len() == arg_args.len() => {
            args
          }
          _ => arg_args.clone(),
        };

        for ((param_arg, regular), const_) in args.into_iter().zip(arg_args.into_iter()).zip(const_args.into_iter()) {
          self.constrain(
            param_arg,
            ArgPair {
              regular,
              const_,
            },
            variance,
          );
        }
      }
      TypeKind::Object(obj_id) => {
        let TypeKind::Object(arg_obj) = self.store.type_kind(arg.regular) else {
          return;
        };
        let param_shape = self.store.shape(self.store.object(obj_id).shape);
        let regular_shape = self.store.shape(self.store.object(arg_obj).shape);
        let const_shape = match self.store.type_kind(arg.const_) {
          TypeKind::Object(obj) => self.store.shape(self.store.object(obj).shape),
          _ => regular_shape.clone(),
        };
        self.constrain_shapes(&param_shape, &regular_shape, &const_shape, variance);
      }
      _ => {}
    }
  }

  fn constrain_shapes(
    &mut self,
    param_shape: &Shape,
    regular_shape: &Shape,
    const_shape: &Shape,
    variance: Variance,
  ) {
    for prop in param_shape.properties.iter() {
      let regular_prop = regular_shape.properties.iter().find(|p| p.key == prop.key);
      let const_prop = const_shape.properties.iter().find(|p| p.key == prop.key);
      let Some(regular_prop) = regular_prop.or(const_prop) else {
        continue;
      };
      let regular_ty = regular_prop.data.ty;
      let const_ty = const_prop.map(|p| p.data.ty).unwrap_or(regular_ty);
      self.constrain(
        prop.data.ty,
        ArgPair {
          regular: regular_ty,
          const_: const_ty,
        },
        variance,
      );
    }

    for (param_sig, arg_sig) in param_shape
      .call_signatures
      .iter()
      .zip(regular_shape.call_signatures.iter())
    {
      let p = self.store.signature(*param_sig);
      let a = self.store.signature(*arg_sig);
      self.constrain_signature(&p, &a, variance);
    }
  }

  fn constrain_signature(&mut self, expected: &Signature, actual: &Signature, variance: Variance) {
    let param_variance = variance.flip();
    for (param, arg) in expected.params.iter().zip(actual.params.iter()) {
      self.constrain(
        param.ty,
        ArgPair {
          regular: arg.ty,
          const_: arg.ty,
        },
        param_variance,
      );
    }
    self.constrain(
      expected.ret,
      ArgPair {
        regular: actual.ret,
        const_: actual.ret,
      },
      variance,
    );
  }

  fn contains_inferable_type_param(
    &self,
    ty: TypeId,
    visited: &mut HashSet<TypeId>,
  ) -> bool {
    if !visited.insert(ty) {
      return false;
    }
    match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => self.decls.contains_key(&id),
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .into_iter()
        .any(|member| self.contains_inferable_type_param(member, visited)),
      TypeKind::Array { ty, .. } => self.contains_inferable_type_param(ty, visited),
      TypeKind::Tuple(elems) => elems
        .into_iter()
        .any(|elem| self.contains_inferable_type_param(elem.ty, visited)),
      TypeKind::Callable { overloads } => overloads.into_iter().any(|sig| {
        let sig = self.store.signature(sig);
        sig
          .params
          .into_iter()
          .any(|param| self.contains_inferable_type_param(param.ty, visited))
          || self.contains_inferable_type_param(sig.ret, visited)
      }),
      TypeKind::Ref { args, .. } => args
        .into_iter()
        .any(|arg| self.contains_inferable_type_param(arg, visited)),
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        shape
          .properties
          .into_iter()
          .any(|prop| self.contains_inferable_type_param(prop.data.ty, visited))
          || shape
            .call_signatures
            .into_iter()
            .any(|sig| self.contains_inferable_type_param(self.store.signature(sig).ret, visited))
          || shape.construct_signatures.into_iter().any(|sig| {
            let sig = self.store.signature(sig);
            sig
              .params
              .into_iter()
              .any(|param| self.contains_inferable_type_param(param.ty, visited))
              || self.contains_inferable_type_param(sig.ret, visited)
          })
      }
      _ => false,
    }
  }

  fn add_bound(&mut self, id: TypeParamId, variance: Variance, ty: TypeId) {
    let entry = self.bounds.entry(id).or_default();
    match variance {
      Variance::Covariant => entry.lower.push(ty),
      Variance::Contravariant => entry.upper.push(ty),
    }
  }

  fn solve(&self, order: &[TypeParamId]) -> InferenceResult {
    let mut result = InferenceResult::default();
    let primitives = self.store.primitive_ids();

    for tp in order.iter() {
      let decl = self
        .decls
        .get(tp)
        .cloned()
        .unwrap_or_else(|| TypeParamDecl::new(*tp));
      let bounds = self.bounds.get(tp).cloned().unwrap_or_default();

      let mut substituter = Substituter::new(Arc::clone(&self.store), result.substitutions.clone());
      let mut lowers: Vec<TypeId> = bounds
        .lower
        .into_iter()
        .map(|ty| substituter.substitute_type(ty))
        .collect();
      let mut uppers: Vec<TypeId> = bounds
        .upper
        .into_iter()
        .map(|ty| substituter.substitute_type(ty))
        .collect();

      lowers.sort_unstable();
      lowers.dedup();
      uppers.sort_unstable();
      uppers.dedup();

      let constraint = decl.constraint.map(|c| substituter.substitute_type(c));
      let default = decl.default.map(|d| substituter.substitute_type(d));

      let mut candidate: Option<TypeId> = None;
      if !lowers.is_empty() {
        let mut lowers = lowers;
        if lowers.len() > 1 {
          let has_specific = lowers
            .iter()
            .any(|b| !matches!(self.store.type_kind(*b), TypeKind::Unknown | TypeKind::Any));
          if has_specific {
            lowers.retain(|b| !matches!(self.store.type_kind(*b), TypeKind::Unknown | TypeKind::Any));
          }
        }
        candidate = Some(if lowers.len() == 1 {
          lowers[0]
        } else {
          self.store.union(lowers)
        });
      }
      if candidate.is_none() && !uppers.is_empty() {
        candidate = Some(if uppers.len() == 1 {
          uppers[0]
        } else {
          self.store.intersection(uppers.clone())
        });
      }
      if candidate.is_none() {
        candidate = default;
      }
      let mut candidate = candidate.unwrap_or(primitives.unknown);
      if !decl.const_ {
        candidate = widen_inferred_candidate(self.store.as_ref(), candidate);
      }

      if !uppers.is_empty() {
        let upper = if uppers.len() == 1 {
          uppers[0]
        } else {
          self.store.intersection(uppers.clone())
        };
        if !self.relate.is_assignable(candidate, upper) {
          candidate = self.store.intersection(vec![candidate, upper]);
        }
      }

      if let Some(constraint) = constraint {
        if !self.relate.is_assignable(candidate, constraint) {
          result.diagnostics.push(InferenceDiagnostic {
            param: *tp,
            constraint,
            actual: candidate,
            message: format!(
              "inferred type argument T{} = {} is not assignable to constraint {}",
              tp.0,
              TypeDisplay::new(self.store.as_ref(), candidate),
              TypeDisplay::new(self.store.as_ref(), constraint)
            ),
          });
          candidate = self.store.intersection(vec![candidate, constraint]);
        }
      }

      result.substitutions.insert(*tp, candidate);
    }

    result
  }
}

fn widen_inferred_candidate(store: &TypeStore, ty: TypeId) -> TypeId {
  let prim = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut all_number = true;
      let mut all_string = true;
      let mut all_boolean = true;
      let mut all_bigint = true;
      for member in members {
        match store.type_kind(member) {
          TypeKind::NumberLiteral(_) => {}
          _ => all_number = false,
        }
        match store.type_kind(member) {
          TypeKind::StringLiteral(_) => {}
          _ => all_string = false,
        }
        match store.type_kind(member) {
          TypeKind::BooleanLiteral(_) => {}
          _ => all_boolean = false,
        }
        match store.type_kind(member) {
          TypeKind::BigIntLiteral(_) => {}
          _ => all_bigint = false,
        }
      }
      if all_number {
        prim.number
      } else if all_string {
        prim.string
      } else if all_boolean {
        prim.boolean
      } else if all_bigint {
        prim.bigint
      } else {
        ty
      }
    }
    _ => ty,
  }
}
