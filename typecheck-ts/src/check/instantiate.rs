use std::collections::HashMap;
use std::sync::Arc;

use smallvec::SmallVec;
use types_ts_interned::ShapeId;
use types_ts_interned::{
  CacheConfig, CacheStats, ObjectType, Shape, ShardedCache, Signature, SignatureId, TupleElem,
  TypeId, TypeKind, TypeParamDecl, TypeParamId, TypeStore,
};

/// Budgets for a single substitution walk.
///
/// Instantiation can explode on recursive generics; these caps make pathology
/// fail fast instead of allocating unbounded interned types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstantiationLimits {
  pub max_depth: usize,
  pub max_steps: usize,
}

impl InstantiationLimits {
  pub const DEFAULT_MAX_DEPTH: usize = 128;
  pub const DEFAULT_MAX_STEPS: usize = 50_000;
}

impl Default for InstantiationLimits {
  fn default() -> Self {
    Self {
      max_depth: Self::DEFAULT_MAX_DEPTH,
      max_steps: Self::DEFAULT_MAX_STEPS,
    }
  }
}

/// Performs type parameter substitution over [`TypeKind`] trees.
///
/// The substituter owns its own memoization tables so it can be reused to
/// instantiate multiple related types or signatures with the same mapping.
#[derive(Debug)]
pub struct Substituter {
  store: Arc<TypeStore>,
  subst: HashMap<TypeParamId, TypeId>,
  type_cache: HashMap<TypeId, TypeId>,
  signature_cache: HashMap<SignatureId, SignatureId>,
  shape_cache: HashMap<ShapeId, ShapeId>,
  limits: InstantiationLimits,
  steps: usize,
  budget_exceeded: bool,
}

impl Substituter {
  /// Create a new substituter over a shared [`TypeStore`].
  pub fn new(store: Arc<TypeStore>, subst: HashMap<TypeParamId, TypeId>) -> Self {
    Self {
      store,
      subst,
      type_cache: HashMap::new(),
      signature_cache: HashMap::new(),
      shape_cache: HashMap::new(),
      limits: InstantiationLimits::default(),
      steps: 0,
      budget_exceeded: false,
    }
  }

  pub fn with_limits(mut self, limits: InstantiationLimits) -> Self {
    self.limits = limits;
    self
  }

  pub fn budget_exceeded(&self) -> bool {
    self.budget_exceeded
  }

  /// Substitute type parameters inside a [`Signature`], returning the interned
  /// [`SignatureId`] for the instantiated signature.
  pub fn substitute_signature(&mut self, sig: &Signature) -> SignatureId {
    self.substitute_signature_at(sig, 0)
  }

  fn substitute_signature_at(&mut self, sig: &Signature, depth: usize) -> SignatureId {
    let mut instantiated = sig.clone();
    for param in instantiated.params.iter_mut() {
      param.ty = self.substitute_type_at(param.ty, depth);
    }
    instantiated.ret = self.substitute_type_at(instantiated.ret, depth);
    if let Some(this) = instantiated.this_param.as_mut() {
      *this = self.substitute_type_at(*this, depth);
    }
    instantiated.type_params = instantiated
      .type_params
      .iter()
      .filter_map(|tp| {
        if self.subst.contains_key(&tp.id) {
          return None;
        }
        Some(TypeParamDecl {
          id: tp.id,
          constraint: tp.constraint.map(|c| self.substitute_type_at(c, depth)),
          default: tp.default.map(|d| self.substitute_type_at(d, depth)),
          variance: tp.variance,
          const_: tp.const_,
        })
      })
      .collect();
    self.store.intern_signature(instantiated)
  }

  /// Substitute type parameters inside a [`SignatureId`].
  pub fn substitute_signature_id(&mut self, id: SignatureId) -> SignatureId {
    self.substitute_signature_id_at(id, 0)
  }

  fn substitute_signature_id_at(&mut self, id: SignatureId, depth: usize) -> SignatureId {
    if let Some(hit) = self.signature_cache.get(&id) {
      return *hit;
    }
    let sig = self.store.signature(id);
    let instantiated = self.substitute_signature_at(&sig, depth);
    self.signature_cache.insert(id, instantiated);
    instantiated
  }

  /// Substitute type parameters inside a [`TypeId`], returning the instantiated
  /// interned type.
  pub fn substitute_type(&mut self, ty: TypeId) -> TypeId {
    self.substitute_type_at(ty, 0)
  }

  fn substitute_type_at(&mut self, ty: TypeId, depth: usize) -> TypeId {
    if depth >= self.limits.max_depth || self.steps >= self.limits.max_steps {
      self.budget_exceeded = true;
      return ty;
    }
    self.steps += 1;
    if let Some(hit) = self.type_cache.get(&ty) {
      return *hit;
    }
    let next = depth + 1;
    let instantiated = match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => self.subst.get(&id).copied().unwrap_or(ty),
      TypeKind::Union(members) => {
        let mapped = members
          .into_iter()
          .map(|m| self.substitute_type_at(m, next))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped = members
          .into_iter()
          .map(|m| self.substitute_type_at(m, next))
          .collect();
        self.store.intersection(mapped)
      }
      TypeKind::Array { ty, readonly } => {
        let inner = self.substitute_type_at(ty, next);
        self.store.intern_type(TypeKind::Array {
          ty: inner,
          readonly,
        })
      }
      TypeKind::Tuple(elems) => {
        let mapped: Vec<TupleElem> = elems
          .into_iter()
          .map(|elem| TupleElem {
            ty: self.substitute_type_at(elem.ty, next),
            optional: elem.optional,
            rest: elem.rest,
            readonly: elem.readonly,
          })
          .collect();
        self.store.intern_type(TypeKind::Tuple(mapped))
      }
      TypeKind::Callable { overloads } => {
        let mapped: Vec<SignatureId> = overloads
          .into_iter()
          .map(|id| self.substitute_signature_id_at(id, next))
          .collect();
        self
          .store
          .intern_type(TypeKind::Callable { overloads: mapped })
      }
      TypeKind::Ref { def, args } => {
        let mapped_args = args
          .into_iter()
          .map(|arg| self.substitute_type_at(arg, next))
          .collect();
        self.store.intern_type(TypeKind::Ref {
          def,
          args: mapped_args,
        })
      }
      TypeKind::Object(obj_id) => {
        let mapped = self.substitute_object_at(obj_id, next);
        self.store.intern_type(TypeKind::Object(mapped))
      }
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => {
        let check = self.substitute_type_at(check, next);
        let extends = self.substitute_type_at(extends, next);
        let true_ty = self.substitute_type_at(true_ty, next);
        let false_ty = self.substitute_type_at(false_ty, next);
        self.store.intern_type(TypeKind::Conditional {
          check,
          extends,
          true_ty,
          false_ty,
          distributive,
        })
      }
      TypeKind::Mapped(mapped) => {
        let mut mapped = mapped.clone();
        mapped.source = self.substitute_type_at(mapped.source, next);
        mapped.value = self.substitute_type_at(mapped.value, next);
        if let Some(name_type) = mapped.name_type.as_mut() {
          *name_type = self.substitute_type_at(*name_type, next);
        }
        if let Some(as_type) = mapped.as_type.as_mut() {
          *as_type = self.substitute_type_at(*as_type, next);
        }
        self.store.intern_type(TypeKind::Mapped(mapped))
      }
      TypeKind::TemplateLiteral(mut tpl) => {
        for chunk in tpl.spans.iter_mut() {
          chunk.ty = self.substitute_type_at(chunk.ty, next);
        }
        self.store.intern_type(TypeKind::TemplateLiteral(tpl))
      }
      TypeKind::Intrinsic { kind, ty } => {
        let ty = self.substitute_type_at(ty, next);
        self.store.intern_type(TypeKind::Intrinsic { kind, ty })
      }
      TypeKind::IndexedAccess { obj, index } => {
        let obj = self.substitute_type_at(obj, next);
        let index = self.substitute_type_at(index, next);
        self
          .store
          .intern_type(TypeKind::IndexedAccess { obj, index })
      }
      TypeKind::KeyOf(inner) => {
        let inner = self.substitute_type_at(inner, next);
        self.store.intern_type(TypeKind::KeyOf(inner))
      }
      _other => {
        // Primitive, literal, `this`, `infer`, etc. remain unchanged.
        self.store.canon(ty)
      }
    };
    self.type_cache.insert(ty, instantiated);
    instantiated
  }

  fn substitute_object_at(
    &mut self,
    obj: types_ts_interned::ObjectId,
    depth: usize,
  ) -> types_ts_interned::ObjectId {
    let obj_data = self.store.object(obj);
    let shape_id = self.substitute_shape_at(obj_data.shape, depth);
    self.store.intern_object(ObjectType { shape: shape_id })
  }

  fn substitute_shape_at(&mut self, shape_id: ShapeId, depth: usize) -> ShapeId {
    if let Some(hit) = self.shape_cache.get(&shape_id) {
      return *hit;
    }
    let mut shape: Shape = self.store.shape(shape_id);
    for prop in shape.properties.iter_mut() {
      prop.data.ty = self.substitute_type_at(prop.data.ty, depth);
    }
    for idx in shape.indexers.iter_mut() {
      idx.key_type = self.substitute_type_at(idx.key_type, depth);
      idx.value_type = self.substitute_type_at(idx.value_type, depth);
    }
    for sig in shape.call_signatures.iter_mut() {
      *sig = self.substitute_signature_id_at(*sig, depth);
    }
    for sig in shape.construct_signatures.iter_mut() {
      *sig = self.substitute_signature_id_at(*sig, depth);
    }
    let mapped = self.store.intern_shape(shape);
    self.shape_cache.insert(shape_id, mapped);
    mapped
  }
}

/// Caches instantiations of a particular definition for repeated calls.
#[derive(Clone, Debug)]
pub struct InstantiationCache {
  signature_cache: Arc<ShardedCache<InstantiationKey, SignatureId>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct InstantiationKey {
  sig: SignatureId,
  args: SmallVec<[TypeId; 4]>,
}

impl Default for InstantiationCache {
  fn default() -> Self {
    Self::with_config(CacheConfig::default())
  }
}

impl InstantiationCache {
  pub fn with_config(config: CacheConfig) -> Self {
    Self {
      signature_cache: Arc::new(ShardedCache::new(config)),
    }
  }

  pub fn stats(&self) -> CacheStats {
    self.signature_cache.stats()
  }

  pub fn clear(&self) {
    self.signature_cache.clear();
  }

  /// Instantiate a signature for a specific definition and type argument mapping,
  /// caching the result to avoid re-instantiating identical substitutions.
  pub fn instantiate_signature(
    &self,
    store: &Arc<TypeStore>,
    sig_id: SignatureId,
    sig: &Signature,
    subst: &HashMap<TypeParamId, TypeId>,
  ) -> SignatureId {
    if sig.type_params.is_empty() {
      return sig_id;
    }
    let unknown = store.primitive_ids().unknown;
    let mut key_args: SmallVec<[TypeId; 4]> = SmallVec::with_capacity(sig.type_params.len());
    for tp in sig.type_params.iter() {
      key_args.push(subst.get(&tp.id).copied().unwrap_or(unknown));
    }
    let cache_key = InstantiationKey {
      sig: sig_id,
      args: key_args,
    };
    if let Some(hit) = self.signature_cache.get(&cache_key) {
      return hit;
    }
    let mut substituter = Substituter::new(Arc::clone(store), subst.clone());
    let instantiated = substituter.substitute_signature(sig);
    self.signature_cache.insert(cache_key, instantiated);
    instantiated
  }
}
