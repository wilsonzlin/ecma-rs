use std::collections::HashMap;
use std::sync::Arc;

use smallvec::SmallVec;
use types_ts_interned::{
  CacheConfig, CacheStats, ObjectType, Shape, ShardedCache, Signature, SignatureId, TupleElem,
  TypeId, TypeKind, TypeParamDecl, TypeParamId, TypeStore,
};
use types_ts_interned::ShapeId;

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
    }
  }

  /// Substitute type parameters inside a [`Signature`], returning the interned
  /// [`SignatureId`] for the instantiated signature.
  pub fn substitute_signature(&mut self, sig: &Signature) -> SignatureId {
    let mut instantiated = sig.clone();
    for param in instantiated.params.iter_mut() {
      param.ty = self.substitute_type(param.ty);
    }
    instantiated.ret = self.substitute_type(instantiated.ret);
    if let Some(this) = instantiated.this_param.as_mut() {
      *this = self.substitute_type(*this);
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
          constraint: tp.constraint.map(|c| self.substitute_type(c)),
          default: tp.default.map(|d| self.substitute_type(d)),
          variance: tp.variance,
        })
      })
      .collect();
    self.store.intern_signature(instantiated)
  }

  /// Substitute type parameters inside a [`SignatureId`].
  pub fn substitute_signature_id(&mut self, id: SignatureId) -> SignatureId {
    if let Some(hit) = self.signature_cache.get(&id) {
      return *hit;
    }
    let sig = self.store.signature(id);
    let instantiated = self.substitute_signature(&sig);
    self.signature_cache.insert(id, instantiated);
    instantiated
  }

  /// Substitute type parameters inside a [`TypeId`], returning the instantiated
  /// interned type.
  pub fn substitute_type(&mut self, ty: TypeId) -> TypeId {
    if let Some(hit) = self.type_cache.get(&ty) {
      return *hit;
    }
    let instantiated = match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => self.subst.get(&id).copied().unwrap_or(ty),
      TypeKind::Union(members) => {
        let mapped = members
          .into_iter()
          .map(|m| self.substitute_type(m))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped = members
          .into_iter()
          .map(|m| self.substitute_type(m))
          .collect();
        self.store.intersection(mapped)
      }
      TypeKind::Array { ty, readonly } => {
        let inner = self.substitute_type(ty);
        self.store.intern_type(TypeKind::Array {
          ty: inner,
          readonly,
        })
      }
      TypeKind::Tuple(elems) => {
        let mapped: Vec<TupleElem> = elems
          .into_iter()
          .map(|elem| TupleElem {
            ty: self.substitute_type(elem.ty),
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
          .map(|id| self.substitute_signature_id(id))
          .collect();
        self
          .store
          .intern_type(TypeKind::Callable { overloads: mapped })
      }
      TypeKind::Ref { def, args } => {
        let mapped_args = args
          .into_iter()
          .map(|arg| self.substitute_type(arg))
          .collect();
        self.store.intern_type(TypeKind::Ref {
          def,
          args: mapped_args,
        })
      }
      TypeKind::Object(obj_id) => {
        let mapped = self.substitute_object(obj_id);
        self.store.intern_type(TypeKind::Object(mapped))
      }
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => {
        let check = self.substitute_type(check);
        let extends = self.substitute_type(extends);
        let true_ty = self.substitute_type(true_ty);
        let false_ty = self.substitute_type(false_ty);
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
        mapped.source = self.substitute_type(mapped.source);
        mapped.value = self.substitute_type(mapped.value);
        if let Some(name_type) = mapped.name_type.as_mut() {
          *name_type = self.substitute_type(*name_type);
        }
        if let Some(as_type) = mapped.as_type.as_mut() {
          *as_type = self.substitute_type(*as_type);
        }
        self.store.intern_type(TypeKind::Mapped(mapped))
      }
      TypeKind::TemplateLiteral(mut tpl) => {
        for chunk in tpl.spans.iter_mut() {
          chunk.ty = self.substitute_type(chunk.ty);
        }
        self.store.intern_type(TypeKind::TemplateLiteral(tpl))
      }
      TypeKind::IndexedAccess { obj, index } => {
        let obj = self.substitute_type(obj);
        let index = self.substitute_type(index);
        self
          .store
          .intern_type(TypeKind::IndexedAccess { obj, index })
      }
      TypeKind::KeyOf(inner) => {
        let inner = self.substitute_type(inner);
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

  fn substitute_object(&mut self, obj: types_ts_interned::ObjectId) -> types_ts_interned::ObjectId {
    let obj_data = self.store.object(obj);
    let shape_id = self.substitute_shape(obj_data.shape);
    self.store.intern_object(ObjectType { shape: shape_id })
  }

  fn substitute_shape(&mut self, shape_id: ShapeId) -> ShapeId {
    if let Some(hit) = self.shape_cache.get(&shape_id) {
      return *hit;
    }
    let mut shape: Shape = self.store.shape(shape_id);
    for prop in shape.properties.iter_mut() {
      prop.data.ty = self.substitute_type(prop.data.ty);
    }
    for idx in shape.indexers.iter_mut() {
      idx.key_type = self.substitute_type(idx.key_type);
      idx.value_type = self.substitute_type(idx.value_type);
    }
    for sig in shape.call_signatures.iter_mut() {
      *sig = self.substitute_signature_id(*sig);
    }
    for sig in shape.construct_signatures.iter_mut() {
      *sig = self.substitute_signature_id(*sig);
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
    let cache_key = InstantiationKey { sig: sig_id, args: key_args };
    if let Some(hit) = self.signature_cache.get(&cache_key) {
      return hit;
    }
    let mut substituter = Substituter::new(Arc::clone(store), subst.clone());
    let instantiated = substituter.substitute_signature(sig);
    self.signature_cache.insert(cache_key, instantiated);
    instantiated
  }
}
