use std::collections::HashMap;
use std::sync::Arc;

use super::instantiate::Substituter;
use types_ts_interned::{Shape, Signature, TypeId, TypeKind, TypeParamId, TypeStore};

/// Definition for a single type parameter, including constraint and default.
#[derive(Clone, Debug)]
pub struct TypeParamDecl {
  pub id: TypeParamId,
  pub constraint: Option<TypeId>,
  pub default: Option<TypeId>,
}

impl TypeParamDecl {
  pub fn new(id: TypeParamId) -> Self {
    Self {
      id,
      constraint: None,
      default: None,
    }
  }
}

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
/// The caller is responsible for providing the [`TypeParamDecl`] metadata for
/// the signature's [`Signature::type_params`]. Inference proceeds by relating
/// the declared parameter types against the provided argument types, collecting
/// lower and upper bounds for each type parameter depending on variance.
pub fn infer_type_arguments_for_call(
  store: &Arc<TypeStore>,
  sig: &Signature,
  type_params: &[TypeParamDecl],
  args: &[TypeId],
  contextual_return: Option<TypeId>,
) -> InferenceResult {
  let mut decls: HashMap<TypeParamId, TypeParamDecl> = type_params
    .iter()
    .map(|decl| (decl.id, decl.clone()))
    .collect();
  for tp in sig.type_params.iter() {
    decls.entry(*tp).or_insert_with(|| TypeParamDecl::new(*tp));
  }

  let mut ctx = InferenceContext::new(Arc::clone(store), decls);

  for (param, arg) in sig.params.iter().zip(args.iter()) {
    ctx.constrain(param.ty, *arg, Variance::Covariant);
  }

  if let Some(ret) = contextual_return {
    ctx.constrain(sig.ret, ret, Variance::Covariant);
  }

  ctx.solve(&sig.type_params)
}

#[derive(Clone, Copy, Debug)]
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

struct InferenceContext {
  store: Arc<TypeStore>,
  bounds: HashMap<TypeParamId, Bounds>,
  decls: HashMap<TypeParamId, TypeParamDecl>,
}

impl InferenceContext {
  fn new(store: Arc<TypeStore>, decls: HashMap<TypeParamId, TypeParamDecl>) -> Self {
    Self {
      store,
      bounds: HashMap::new(),
      decls,
    }
  }

  fn constrain(&mut self, param_ty: TypeId, arg_ty: TypeId, variance: Variance) {
    if param_ty == arg_ty {
      return;
    }

    match self.store.type_kind(arg_ty) {
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          self.constrain(param_ty, member, variance);
        }
        return;
      }
      _ => {}
    }

    match self.store.type_kind(param_ty) {
      TypeKind::TypeParam(id) => {
        self.add_bound(id, variance, arg_ty);
      }
      TypeKind::Union(options) => {
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
            self.constrain(ty, elem.ty, variance);
          }
        }
        _ => {}
      },
      TypeKind::Tuple(param_elems) => match self.store.type_kind(arg_ty) {
        TypeKind::Tuple(arg_elems) => {
          let mut arg_iter = arg_elems.into_iter();
          for param_elem in param_elems {
            if param_elem.rest {
              for arg_elem in arg_iter {
                self.constrain(param_elem.ty, arg_elem.ty, variance);
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

  fn constrain_signature(
    &mut self,
    expected: &Signature,
    actual: &Signature,
    variance: Variance,
  ) {
    let param_variance = variance.flip();
    for (param, arg) in expected.params.iter().zip(actual.params.iter()) {
      self.constrain(param.ty, arg.ty, param_variance);
    }
    self.constrain(expected.ret, actual.ret, variance);
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
      let mut candidate: Option<TypeId> = None;
      if !bounds.lower.is_empty() {
        candidate = Some(if bounds.lower.len() == 1 {
          bounds.lower[0]
        } else {
          self.store.union(bounds.lower.clone())
        });
      }
      if candidate.is_none() && !bounds.upper.is_empty() {
        candidate = Some(if bounds.upper.len() == 1 {
          bounds.upper[0]
        } else {
          self.store.intersection(bounds.upper.clone())
        });
      }
      if candidate.is_none() {
        if let Some(default) = decl.default {
          let mut substituter =
            Substituter::new(Arc::clone(&self.store), result.substitutions.clone());
          candidate = Some(substituter.substitute_type(default));
        }
      }
      let mut candidate = candidate.unwrap_or(primitives.unknown);

      if !bounds.upper.is_empty() {
        let upper = if bounds.upper.len() == 1 {
          bounds.upper[0]
        } else {
          self.store.intersection(bounds.upper.clone())
        };
        if !is_assignable(self.store.as_ref(), candidate, upper) {
          candidate = self.store.intersection(vec![candidate, upper]);
        }
      }

      if let Some(constraint) = decl.constraint {
        if !is_assignable(self.store.as_ref(), candidate, constraint) {
          result.diagnostics.push(InferenceDiagnostic {
            param: *tp,
            constraint,
            actual: candidate,
            message: format!("type argument for {:?} does not satisfy constraint", tp),
          });
          candidate = self.store.intersection(vec![candidate, constraint]);
        }
      }

      result.substitutions.insert(*tp, candidate);
    }

    result
  }
}

fn is_assignable(store: &TypeStore, src: TypeId, dst: TypeId) -> bool {
  if src == dst {
    return true;
  }
  let primitives = store.primitive_ids();
  let src_kind = store.type_kind(src);
  let dst_kind = store.type_kind(dst);

  match dst_kind {
    TypeKind::Any | TypeKind::Unknown => return true,
    _ => {}
  }
  match src_kind {
    TypeKind::Never => return true,
    TypeKind::Any => return true,
    _ => {}
  }

  match (&src_kind, &dst_kind) {
    (TypeKind::NumberLiteral(_), TypeKind::Number)
    | (TypeKind::StringLiteral(_), TypeKind::String)
    | (TypeKind::BooleanLiteral(_), TypeKind::Boolean)
    | (TypeKind::BigIntLiteral(_), TypeKind::BigInt)
    | (TypeKind::UniqueSymbol, TypeKind::Symbol) => return true,
    _ => {}
  }

  if let TypeKind::Union(members) = &src_kind {
    return members
      .iter()
      .all(|member| is_assignable(store, *member, dst));
  }
  if let TypeKind::Union(options) = &dst_kind {
    return options
      .iter()
      .any(|member| is_assignable(store, src, *member));
  }

  if let TypeKind::Intersection(parts) = &dst_kind {
    return parts
      .iter()
      .all(|member| is_assignable(store, src, *member));
  }
  if let TypeKind::Intersection(parts) = &src_kind {
    return parts
      .iter()
      .all(|member| is_assignable(store, *member, dst));
  }

  match (&src_kind, &dst_kind) {
    (TypeKind::Number, TypeKind::Number)
    | (TypeKind::String, TypeKind::String)
    | (TypeKind::Boolean, TypeKind::Boolean)
    | (TypeKind::Null, TypeKind::Null)
    | (TypeKind::Undefined, TypeKind::Undefined) => return true,
    (TypeKind::Array { ty: src_ty, .. }, TypeKind::Array { ty: dst_ty, .. }) => {
      return is_assignable(store, *src_ty, *dst_ty)
    }
    (TypeKind::Tuple(src_elems), TypeKind::Tuple(dst_elems)) => {
      if src_elems.len() != dst_elems.len() {
        return false;
      }
      for (src_elem, dst_elem) in src_elems.iter().zip(dst_elems.iter()) {
        if !is_assignable(store, src_elem.ty, dst_elem.ty) {
          return false;
        }
      }
      return true;
    }
    (
      TypeKind::Callable {
        overloads: src_overloads,
      },
      TypeKind::Callable {
        overloads: dst_overloads,
      },
    ) => {
      if let (Some(src_sig), Some(dst_sig)) = (src_overloads.first(), dst_overloads.first()) {
        let src_sig = store.signature(*src_sig);
        let dst_sig = store.signature(*dst_sig);
        return is_signature_assignable(store, &src_sig, &dst_sig);
      }
    }
    (TypeKind::Ref { def: a_def, args: a_args }, TypeKind::Ref { def: b_def, args: b_args }) => {
      if a_def == b_def && a_args.len() == b_args.len() {
        return a_args
          .iter()
          .zip(b_args.iter())
          .all(|(a, b)| is_assignable(store, *a, *b));
      }
    }
    (TypeKind::Object(a_obj), TypeKind::Object(b_obj)) => {
      let a_shape = store.shape(store.object(*a_obj).shape);
      let b_shape = store.shape(store.object(*b_obj).shape);
      return is_shape_assignable(store, &a_shape, &b_shape);
    }
    (TypeKind::TypeParam(_), _) | (_, TypeKind::TypeParam(_)) => return true,
    _ => {}
  }

  // Fallback: only exact match or `unknown`/`any` handled above.
  if dst == primitives.unknown {
    return true;
  }

  false
}

fn is_shape_assignable(store: &TypeStore, src: &Shape, dst: &Shape) -> bool {
  for prop in dst.properties.iter() {
    if let Some(src_prop) = src.properties.iter().find(|p| p.key == prop.key) {
      if !is_assignable(store, src_prop.data.ty, prop.data.ty) {
        return false;
      }
    } else {
      return false;
    }
  }

  true
}

fn is_signature_assignable(store: &TypeStore, src: &Signature, dst: &Signature) -> bool {
  if src.params.len() != dst.params.len() {
    return false;
  }

  for (src_param, dst_param) in src.params.iter().zip(dst.params.iter()) {
    if !is_assignable(store, dst_param.ty, src_param.ty) {
      return false;
    }
  }

  is_assignable(store, src.ret, dst.ret)
}
