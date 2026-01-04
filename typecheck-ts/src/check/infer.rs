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
    if let TypeKind::TypeParam(tp) = store.type_kind(sig.params[rest_index].ty) {
      if ctx.decls.contains_key(&tp) {
        let rest_args = args.get(rest_index..).unwrap_or(&[]);
        let inferred = infer_variadic_rest_tuple(store.as_ref(), rest_args);
        ctx.add_bound(tp, Variance::Covariant, inferred);
        skip_from_index = Some(rest_index);
      }
    }
  }

  for (idx, arg) in args.iter().enumerate() {
    if skip_from_index.is_some_and(|skip| idx >= skip) {
      break;
    }
    let Some(expected) = expected_arg_type_at(store.as_ref(), sig, idx) else {
      continue;
    };
    let actual = if arg.spread {
      relate.spread_element_type(arg.ty)
    } else {
      arg.ty
    };
    ctx.constrain(expected, actual, Variance::Covariant);
  }

  if let Some(ret) = contextual_return {
    ctx.constrain(sig.ret, ret, Variance::Covariant);
  }

  let order: Vec<TypeParamId> = sig.type_params.iter().map(|tp| tp.id).collect();
  ctx.solve(&order)
}

fn infer_variadic_rest_tuple(store: &TypeStore, rest_args: &[CallArgType]) -> TypeId {
  if let [only] = rest_args {
    if only.spread {
      match store.type_kind(only.ty) {
        // For `f<T extends any[]>(...args: T)` and `f(...arr)` where `arr` is a
        // non-tuple array, `tsc` infers `T` as the array type (not `[...T]`).
        TypeKind::Array { .. }
        // Tuple spreads are expanded by the caller (overload checker) when the
        // tuple type is known; but if a raw spread tuple arrives, preserve it.
        | TypeKind::Tuple(_) => return only.ty,
        _ => {}
      }
    }
  }

  let elems: Vec<TupleElem> = rest_args
    .iter()
    .map(|arg| TupleElem {
      ty: arg.ty,
      optional: false,
      rest: arg.spread,
      readonly: false,
    })
    .collect();
  store.intern_type(TypeKind::Tuple(elems))
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

  fn constrain(&mut self, param_ty: TypeId, arg_ty: TypeId, variance: Variance) {
    if param_ty == arg_ty {
      return;
    }

    // Covariant inference distributes unions to gather candidates.
    if variance == Variance::Covariant {
      if let TypeKind::Union(members) = self.store.type_kind(arg_ty) {
        for member in members {
          self.constrain(param_ty, member, variance);
        }
        return;
      }
    }

    match self.store.type_kind(param_ty) {
      TypeKind::TypeParam(id) => {
        if self.decls.contains_key(&id) {
          self.add_bound(id, variance, arg_ty);
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
          self.constrain(opt, arg_ty, variance);
        }
      }
      TypeKind::Intersection(options) => {
        for opt in options {
          self.constrain(opt, arg_ty, variance);
        }
      }
      TypeKind::Array { ty, .. } => match self.store.type_kind(arg_ty) {
        TypeKind::Array { ty: arg_inner, .. } => self.constrain(ty, arg_inner, variance),
        TypeKind::Tuple(elems) => {
          for elem in elems {
            let elem_ty = if elem.rest {
              self.relate.spread_element_type(elem.ty)
            } else {
              elem.ty
            };
            self.constrain(ty, elem_ty, variance);
          }
        }
        _ => {}
      },
      TypeKind::Tuple(param_elems) => match self.store.type_kind(arg_ty) {
        TypeKind::Tuple(arg_elems) => {
          let mut arg_iter = arg_elems.into_iter();
          for param_elem in param_elems {
            if param_elem.rest {
              let expected_elem_ty = self.relate.spread_element_type(param_elem.ty);
              for arg_elem in arg_iter {
                self.constrain(expected_elem_ty, arg_elem.ty, variance);
              }
              break;
            }
            if let Some(arg_elem) = arg_iter.next() {
              self.constrain(param_elem.ty, arg_elem.ty, variance);
            }
          }
        }
        _ => {}
      },
      TypeKind::Callable { overloads } => {
        if let TypeKind::Callable {
          overloads: arg_overloads,
        } = self.store.type_kind(arg_ty)
        {
          if let (Some(param_sig), Some(arg_sig)) = (overloads.first(), arg_overloads.first()) {
            let param_sig = self.store.signature(*param_sig);
            let arg_sig = self.store.signature(*arg_sig);
            self.constrain_signature(&param_sig, &arg_sig, variance);
          }
        }
      }
      TypeKind::Ref { def, args } => {
        if let TypeKind::Ref {
          def: arg_def,
          args: arg_args,
        } = self.store.type_kind(arg_ty)
        {
          if def == arg_def {
            for (param_arg, actual) in args.into_iter().zip(arg_args.into_iter()) {
              self.constrain(param_arg, actual, variance);
            }
          }
        }
      }
      TypeKind::Object(obj_id) => {
        if let TypeKind::Object(arg_obj) = self.store.type_kind(arg_ty) {
          let param_shape = self.store.shape(self.store.object(obj_id).shape);
          let arg_shape = self.store.shape(self.store.object(arg_obj).shape);
          self.constrain_shapes(&param_shape, &arg_shape, variance);
        }
      }
      _ => {}
    }
  }

  fn constrain_shapes(&mut self, param_shape: &Shape, arg_shape: &Shape, variance: Variance) {
    for prop in param_shape.properties.iter() {
      if let Some(arg_prop) = arg_shape.properties.iter().find(|p| p.key == prop.key) {
        self.constrain(prop.data.ty, arg_prop.data.ty, variance);
      }
    }

    for (param_sig, arg_sig) in param_shape
      .call_signatures
      .iter()
      .zip(arg_shape.call_signatures.iter())
    {
      let p = self.store.signature(*param_sig);
      let a = self.store.signature(*arg_sig);
      self.constrain_signature(&p, &a, variance);
    }
  }

  fn constrain_signature(&mut self, expected: &Signature, actual: &Signature, variance: Variance) {
    let param_variance = variance.flip();
    for (param, arg) in expected.params.iter().zip(actual.params.iter()) {
      self.constrain(param.ty, arg.ty, param_variance);
    }
    self.constrain(expected.ret, actual.ret, variance);
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
