use crate::display::TypeDisplay;
use crate::ids::{NameId, ObjectId, ShapeId, SignatureId, TypeId};
use crate::kind::{CompositeKind, TypeKind};
use crate::options::TypeOptions;
use crate::shape::{Indexer, ObjectType, Property, Shape};
use crate::signature::{Param, Signature, TypeParamDecl};
use ahash::RandomState;
use dashmap::mapref::entry::Entry;
use dashmap::DashMap;
use parking_lot::RwLock;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::cmp::Ordering;
use std::collections::HashSet;
use std::hash::{BuildHasher, Hash, Hasher};
use std::sync::Arc;

const HASH_KEY1: u64 = 0x9e37_79b9_7f4a_7c15;
const HASH_KEY2: u64 = 0xc2b2_ae3d_27d4_eb4f;
const HASH_KEY3: u64 = 0x1656_67b1_9e37_79f9;
const HASH_KEY4: u64 = 0x85eb_ca6b_c8f6_9b07;

const TYPE_DOMAIN: u64 = 0x7479_7065;
const SIGNATURE_DOMAIN: u64 = 0x7369_676e;
const SHAPE_DOMAIN: u64 = 0x7368_6170;
const OBJECT_DOMAIN: u64 = 0x6f62_6a65;
const NAME_DOMAIN: u64 = 0x6e61_6d65;

type FingerprintFn = fn(u128, u64, u64) -> u128;

fn stable_state(domain: u64) -> RandomState {
  RandomState::with_seeds(
    HASH_KEY1 ^ domain,
    HASH_KEY2.wrapping_add(domain),
    HASH_KEY3 ^ (domain << 1),
    HASH_KEY4.wrapping_sub(domain),
  )
}

fn stable_hash64<T: Hash>(value: &T, domain: u64, salt: u64) -> u64 {
  let mut hasher = stable_state(domain).build_hasher();
  hasher.write_u64(salt);
  value.hash(&mut hasher);
  hasher.finish()
}

/// Produce a 128-bit fingerprint for a value using domain-separated, stable
/// hashing.
///
/// Two hashes are mixed to make collisions astronomically unlikely. An explicit
/// salt is available so callers can rehash on collision; note that any
/// salt-based collision resolution is necessarily insertion-order dependent
/// because IDs must remain stable once returned.
fn fingerprint<T: Hash>(value: &T, domain: u64, salt: u64) -> u128 {
  let base_salt = salt.wrapping_mul(2);
  let primary = stable_hash64(value, domain, base_salt);
  let secondary = stable_hash64(value, domain, base_salt.wrapping_add(1));
  ((primary as u128) << 64) | secondary as u128
}

fn default_fingerprint(raw: u128, _domain: u64, _salt: u64) -> u128 {
  raw
}

#[derive(Default, Debug)]
struct NameInterner {
  by_name: ahash::AHashMap<String, NameId>,
  by_id: ahash::AHashMap<NameId, String>,
}

impl NameInterner {
  fn hash_name(name: &str, salt: u64) -> NameId {
    NameId(stable_hash64(&name, NAME_DOMAIN, salt))
  }

  fn intern(&mut self, name: impl Into<String>) -> NameId {
    let name = name.into();
    if let Some(id) = self.by_name.get(&name) {
      return *id;
    }

    #[cfg(feature = "strict-determinism")]
    {
      let salt = 0u64;
      let id = Self::hash_name(&name, salt);
      match self.by_id.get(&id) {
        None => {
          self.by_name.insert(name.clone(), id);
          self.by_id.insert(id, name);
          id
        }
        Some(existing) if existing == &name => {
          self.by_name.insert(name.clone(), id);
          id
        }
        Some(existing) => {
          panic!(
            "strict-determinism: name ID collision for {id:?} (existing={existing:?}, new={name:?})"
          );
        }
      }
    }

    #[cfg(not(feature = "strict-determinism"))]
    {
      let mut salt = 0u64;
      loop {
        let id = Self::hash_name(&name, salt);
        match self.by_id.get(&id) {
          None => {
            self.by_name.insert(name.clone(), id);
            self.by_id.insert(id, name);
            return id;
          }
          Some(existing) if existing == &name => {
            self.by_name.insert(name.clone(), id);
            return id;
          }
          Some(_) => {
            salt = salt.wrapping_add(1);
          }
        }
      }
    }
  }

  fn name(&self, id: NameId) -> &str {
    self
      .by_id
      .get(&id)
      .map(|s| s.as_str())
      .expect("NameId not interned")
  }
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PrimitiveIds {
  pub any: TypeId,
  pub unknown: TypeId,
  pub never: TypeId,
  pub void: TypeId,
  pub null: TypeId,
  pub undefined: TypeId,
  pub boolean: TypeId,
  pub number: TypeId,
  pub string: TypeId,
  pub bigint: TypeId,
  pub symbol: TypeId,
  pub unique_symbol: TypeId,
}

/// Thread-safe, interned store for canonicalized types, shapes, objects, names,
/// and signatures.
///
/// IDs are derived from stable hashes of canonical data and are therefore
/// deterministic and thread-scheduling independent **assuming no hash
/// collisions**.
///
/// In the extremely unlikely event of a hash collision, the default
/// configuration falls back to salt-based rehashing. This preserves the
/// invariant that IDs must never change once returned, but it does not define a
/// canonical, order-independent assignment under collisions (the first value
/// inserted keeps the lower-salt ID). Enable the `strict-determinism` feature
/// to treat collisions as an internal error instead.
#[derive(Debug)]
pub struct TypeStore {
  types: DashMap<TypeId, TypeKind, RandomState>,
  shapes: DashMap<ShapeId, Shape, RandomState>,
  objects: DashMap<ObjectId, ObjectType, RandomState>,
  names: RwLock<NameInterner>,
  signatures: DashMap<SignatureId, Signature, RandomState>,
  fingerprint_fn: FingerprintFn,
  options: TypeOptions,
  primitives: PrimitiveIds,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeStoreSnapshot {
  options: TypeOptions,
  primitives: PrimitiveIds,
  types: Vec<(TypeId, TypeKind)>,
  shapes: Vec<(ShapeId, Shape)>,
  objects: Vec<(ObjectId, ObjectType)>,
  signatures: Vec<(SignatureId, Signature)>,
  names: Vec<(NameId, String)>,
}

impl TypeStore {
  fn stable_dedup_signatures(signatures: &mut Vec<SignatureId>) {
    let mut seen = HashSet::new();
    signatures.retain(|sig| seen.insert(*sig));
  }

  fn new_dashmap<K: Eq + Hash, V>(domain: u64) -> DashMap<K, V, RandomState> {
    DashMap::with_hasher(stable_state(domain))
  }

  pub fn new() -> Arc<Self> {
    Self::with_options(TypeOptions::default())
  }

  pub fn with_options(options: TypeOptions) -> Arc<Self> {
    Self::with_options_and_fingerprint(options, default_fingerprint)
  }

  #[doc(hidden)]
  pub fn with_options_and_fingerprint(
    options: TypeOptions,
    fingerprint_fn: fn(u128, u64, u64) -> u128,
  ) -> Arc<Self> {
    let mut store = Self {
      types: Self::new_dashmap(TYPE_DOMAIN),
      shapes: Self::new_dashmap(SHAPE_DOMAIN),
      objects: Self::new_dashmap(OBJECT_DOMAIN),
      names: Default::default(),
      signatures: Self::new_dashmap(SIGNATURE_DOMAIN),
      fingerprint_fn,
      options,
      primitives: PrimitiveIds {
        any: TypeId(0),
        unknown: TypeId(0),
        never: TypeId(0),
        void: TypeId(0),
        null: TypeId(0),
        undefined: TypeId(0),
        boolean: TypeId(0),
        number: TypeId(0),
        string: TypeId(0),
        bigint: TypeId(0),
        symbol: TypeId(0),
        unique_symbol: TypeId(0),
      },
    };

    let primitives = PrimitiveIds {
      any: store.insert_type_direct(TypeKind::Any),
      unknown: store.insert_type_direct(TypeKind::Unknown),
      never: store.insert_type_direct(TypeKind::Never),
      void: store.insert_type_direct(TypeKind::Void),
      null: store.insert_type_direct(TypeKind::Null),
      undefined: store.insert_type_direct(TypeKind::Undefined),
      boolean: store.insert_type_direct(TypeKind::Boolean),
      number: store.insert_type_direct(TypeKind::Number),
      string: store.insert_type_direct(TypeKind::String),
      bigint: store.insert_type_direct(TypeKind::BigInt),
      symbol: store.insert_type_direct(TypeKind::Symbol),
      unique_symbol: store.insert_type_direct(TypeKind::UniqueSymbol),
    };
    store.primitives = primitives;
    Arc::new(store)
  }

  fn fingerprint_value<T: Hash>(&self, value: &T, domain: u64, salt: u64) -> u128 {
    (self.fingerprint_fn)(fingerprint(value, domain, salt), domain, salt)
  }

  fn make_type_id(&self, kind: &TypeKind, salt: u64) -> TypeId {
    TypeId(self.fingerprint_value(kind, TYPE_DOMAIN, salt))
  }

  fn make_signature_id(&self, sig: &Signature, salt: u64) -> SignatureId {
    SignatureId(self.fingerprint_value(sig, SIGNATURE_DOMAIN, salt))
  }

  fn make_shape_id(&self, shape: &Shape, salt: u64) -> ShapeId {
    ShapeId(self.fingerprint_value(shape, SHAPE_DOMAIN, salt))
  }

  fn make_object_id(&self, object: &ObjectType, salt: u64) -> ObjectId {
    ObjectId(self.fingerprint_value(object, OBJECT_DOMAIN, salt))
  }

  /// Insert a value keyed by a fingerprint-derived ID, retrying with an
  /// incremented salt when an occupied entry holds a different value. This
  /// mirrors `NameInterner::intern` but is safe to call from multiple threads.
  ///
  /// Note that collision resolution is deterministic for a fixed insertion
  /// sequence, but does not define a canonical assignment under hash
  /// collisions. When built with the `strict-determinism` feature, collisions
  /// instead cause an immediate panic.
  fn insert_with_collision<T, Id, MakeId>(
    map: &DashMap<Id, T, RandomState>,
    value: T,
    _kind: &str,
    mut make_id: MakeId,
  ) -> Id
  where
    T: Eq,
    Id: Copy + Eq + Hash + std::fmt::Debug,
    MakeId: FnMut(&T, u64) -> Id,
  {
    #[cfg(feature = "strict-determinism")]
    {
      let salt = 0u64;
      let id = make_id(&value, salt);
      match map.entry(id) {
        Entry::Occupied(entry) => {
          if entry.get() == &value {
            return id;
          }
          let next_id = make_id(&value, salt.wrapping_add(1));
          panic!(
            "strict-determinism: {_kind} ID collision for {id:?} (next candidate: {next_id:?})"
          );
        }
        Entry::Vacant(entry) => {
          entry.insert(value);
          return id;
        }
      }
    }

    #[cfg(not(feature = "strict-determinism"))]
    {
      let mut salt = 0u64;
      loop {
        let id = make_id(&value, salt);
        match map.entry(id) {
          Entry::Occupied(entry) => {
            if entry.get() == &value {
              return id;
            }
            salt = salt.wrapping_add(1);
          }
          Entry::Vacant(entry) => {
            entry.insert(value);
            return id;
          }
        }
      }
    }
  }

  fn insert_with_expected_id<T: Eq, Id: Copy + Eq + Hash + std::fmt::Debug>(
    map: &DashMap<Id, T, RandomState>,
    id: Id,
    value: T,
    kind: &str,
  ) -> Id {
    match map.entry(id) {
      Entry::Occupied(entry) => {
        if entry.get() != &value {
          panic!("{kind} ID collision for {id:?}");
        }
        id
      }
      Entry::Vacant(entry) => {
        entry.insert(value);
        id
      }
    }
  }

  fn insert_type_direct(&self, kind: TypeKind) -> TypeId {
    Self::insert_with_collision(&self.types, kind, "type", |value, salt| {
      self.make_type_id(value, salt)
    })
  }

  fn insert_signature_direct(&self, sig: Signature) -> SignatureId {
    Self::insert_with_collision(&self.signatures, sig, "signature", |value, salt| {
      self.make_signature_id(value, salt)
    })
  }

  fn insert_shape_direct(&self, shape: Shape) -> ShapeId {
    Self::insert_with_collision(&self.shapes, shape, "shape", |value, salt| {
      self.make_shape_id(value, salt)
    })
  }

  fn insert_object_direct(&self, object: ObjectType) -> ObjectId {
    Self::insert_with_collision(&self.objects, object, "object", |value, salt| {
      self.make_object_id(value, salt)
    })
  }

  pub fn options(&self) -> TypeOptions {
    self.options
  }

  pub fn primitive_ids(&self) -> PrimitiveIds {
    self.primitives
  }

  pub fn snapshot(&self) -> TypeStoreSnapshot {
    let mut types: Vec<_> = self
      .types
      .iter()
      .map(|entry| (*entry.key(), entry.value().clone()))
      .collect();
    types.sort_by_key(|(id, _)| *id);

    let mut shapes: Vec<_> = self
      .shapes
      .iter()
      .map(|entry| (*entry.key(), entry.value().clone()))
      .collect();
    shapes.sort_by_key(|(id, _)| *id);

    let mut objects: Vec<_> = self
      .objects
      .iter()
      .map(|entry| (*entry.key(), entry.value().clone()))
      .collect();
    objects.sort_by_key(|(id, _)| *id);

    let mut signatures: Vec<_> = self
      .signatures
      .iter()
      .map(|entry| (*entry.key(), entry.value().clone()))
      .collect();
    signatures.sort_by_key(|(id, _)| *id);

    let mut names: Vec<_> = {
      let guard = self.names.read();
      guard
        .by_id
        .iter()
        .map(|(id, name)| (*id, name.clone()))
        .collect()
    };
    names.sort_by_key(|(id, _)| *id);

    TypeStoreSnapshot {
      options: self.options,
      primitives: self.primitives,
      types,
      shapes,
      objects,
      signatures,
      names,
    }
  }

  fn from_snapshot_inner(snapshot: TypeStoreSnapshot) -> Self {
    let TypeStoreSnapshot {
      options,
      primitives,
      types,
      shapes,
      objects,
      signatures,
      names,
    } = snapshot;

    let store = Self {
      types: Self::new_dashmap(TYPE_DOMAIN),
      shapes: Self::new_dashmap(SHAPE_DOMAIN),
      objects: Self::new_dashmap(OBJECT_DOMAIN),
      names: Default::default(),
      signatures: Self::new_dashmap(SIGNATURE_DOMAIN),
      fingerprint_fn: default_fingerprint,
      options,
      primitives,
    };

    {
      let mut interner = store.names.write();
      for (id, name) in names {
        interner.by_id.insert(id, name.clone());
        interner.by_name.insert(name, id);
      }
    }

    for (id, kind) in types {
      Self::insert_with_expected_id(&store.types, id, kind, "type");
    }
    for (id, shape) in shapes {
      Self::insert_with_expected_id(&store.shapes, id, shape, "shape");
    }
    for (id, object) in objects {
      Self::insert_with_expected_id(&store.objects, id, object, "object");
    }
    for (id, sig) in signatures {
      Self::insert_with_expected_id(&store.signatures, id, sig, "signature");
    }

    debug_assert!(store.types.contains_key(&primitives.any));
    debug_assert!(store.types.contains_key(&primitives.unknown));
    debug_assert!(store.types.contains_key(&primitives.never));
    debug_assert!(store.types.contains_key(&primitives.void));
    debug_assert!(store.types.contains_key(&primitives.null));
    debug_assert!(store.types.contains_key(&primitives.undefined));
    debug_assert!(store.types.contains_key(&primitives.boolean));
    debug_assert!(store.types.contains_key(&primitives.number));
    debug_assert!(store.types.contains_key(&primitives.string));
    debug_assert!(store.types.contains_key(&primitives.bigint));
    debug_assert!(store.types.contains_key(&primitives.symbol));
    debug_assert!(store.types.contains_key(&primitives.unique_symbol));

    store
  }

  pub fn from_snapshot(snapshot: TypeStoreSnapshot) -> Arc<Self> {
    Arc::new(Self::from_snapshot_inner(snapshot))
  }

  pub fn name(&self, id: NameId) -> String {
    let guard = self.names.read();
    guard.name(id).to_string()
  }

  pub fn intern_name(&self, name: impl Into<String>) -> NameId {
    self.names.write().intern(name)
  }

  pub fn signature(&self, id: SignatureId) -> Signature {
    self
      .signatures
      .get(&id)
      .map(|entry| entry.value().clone())
      .expect("SignatureId not interned")
  }

  pub fn intern_signature(&self, signature: Signature) -> SignatureId {
    let mut signature = signature;
    for param in signature.params.iter_mut() {
      // Parameter names do not affect TypeScript function type identity, so
      // canonicalize them away while interning to avoid needless duplication.
      param.name = None;
      param.ty = self.canon(param.ty);
    }
    signature.ret = self.canon(signature.ret);
    if let Some(this) = signature.this_param.as_mut() {
      *this = self.canon(*this);
    }
    for tp in signature.type_params.iter_mut() {
      if let Some(constraint) = tp.constraint.as_mut() {
        *constraint = self.canon(*constraint);
      }
      if let Some(default) = tp.default.as_mut() {
        *default = self.canon(*default);
      }
    }
    self.insert_signature_direct(signature)
  }

  pub fn shape(&self, id: ShapeId) -> Shape {
    self
      .shapes
      .get(&id)
      .map(|entry| entry.value().clone())
      .expect("ShapeId not interned")
  }

  pub fn object(&self, id: ObjectId) -> ObjectType {
    self
      .objects
      .get(&id)
      .map(|entry| entry.value().clone())
      .expect("ObjectId not interned")
  }

  pub fn type_kind(&self, id: TypeId) -> TypeKind {
    self
      .types
      .get(&id)
      .map(|entry| entry.value().clone())
      .expect("TypeId not interned")
  }

  pub fn contains_type_id(&self, id: TypeId) -> bool {
    self.types.contains_key(&id)
  }

  pub fn intern_shape(&self, mut shape: Shape) -> ShapeId {
    for prop in shape.properties.iter_mut() {
      prop.data.ty = self.canon(prop.data.ty);
    }
    for idx in shape.indexers.iter_mut() {
      idx.key_type = self.canon(idx.key_type);
      idx.value_type = self.canon(idx.value_type);
    }

    {
      let names = self.names.read();
      shape
        .properties
        .sort_by(|a, b| a.key.cmp_with(&b.key, &|id| names.name(id)));
    }
    // Merge duplicate property keys deterministically by intersecting their
    // types, requiring presence if any declaration is required, propagating
    // readonly if any declaration is readonly, and keeping the most
    // restrictive accessibility modifier if present.
    let mut merged_properties: Vec<Property> = Vec::with_capacity(shape.properties.len());
    let mut declared_on_conflict = false;
    for prop in shape.properties.into_iter() {
      if let Some(last) = merged_properties.last_mut() {
        if last.key == prop.key {
          last.data.ty = self.intersection(vec![last.data.ty, prop.data.ty]);
          last.data.optional = last.data.optional && prop.data.optional;
          last.data.readonly = last.data.readonly || prop.data.readonly;
          last.data.is_method = last.data.is_method || prop.data.is_method;
          match (last.data.declared_on, prop.data.declared_on) {
            (Some(a), Some(b)) if a == b => {}
            (Some(_), Some(_)) => {
              last.data.declared_on = None;
              declared_on_conflict = true;
            }
            (None, Some(b)) => {
              if !declared_on_conflict {
                last.data.declared_on = Some(b);
              }
            }
            _ => {}
          }
          match (last.data.origin, prop.data.origin) {
            (Some(a), Some(b)) if a == b => {}
            (Some(_), Some(_)) => last.data.origin = None,
            (None, Some(b)) => last.data.origin = Some(b),
            _ => {}
          }
          let existing_access = last.data.accessibility.take();
          last.data.accessibility = match (existing_access, prop.data.accessibility) {
            (Some(a), Some(b)) => Some(std::cmp::max(a, b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
          };
          continue;
        }
      }
      merged_properties.push(prop);
      declared_on_conflict = false;
    }
    shape.properties = merged_properties;
    Self::stable_dedup_signatures(&mut shape.call_signatures);
    shape
      .call_signatures
      .sort_by(|a, b| self.signature_cmp(*a, *b));
    Self::stable_dedup_signatures(&mut shape.construct_signatures);
    shape
      .construct_signatures
      .sort_by(|a, b| self.signature_cmp(*a, *b));
    shape.indexers.sort_by(|a, b| {
      self
        .type_cmp(a.key_type, b.key_type)
        .then_with(|| self.type_cmp(a.value_type, b.value_type))
        .then_with(|| a.readonly.cmp(&b.readonly))
    });

    // Merge duplicate index signatures deterministically. Shapes should contain
    // at most one effective indexer per key type (string/number/symbol). When
    // multiple indexers share a key type, their value types combine via
    // intersection (all constraints must be satisfied) and the merged indexer
    // becomes readonly if any constituent is readonly.
    let mut merged_indexers: Vec<Indexer> = Vec::with_capacity(shape.indexers.len());
    for idx in shape.indexers.drain(..) {
      if let Some(last) = merged_indexers.last_mut() {
        if last.key_type == idx.key_type {
          last.value_type = self.intersection(vec![last.value_type, idx.value_type]);
          last.readonly = last.readonly || idx.readonly;
          continue;
        }
      }
      merged_indexers.push(idx);
    }
    shape.indexers = merged_indexers;

    self.insert_shape_direct(shape)
  }

  pub fn intern_object(&self, object: ObjectType) -> ObjectId {
    self.insert_object_direct(object)
  }

  /// Deterministically compare two property keys using the store's interned
  /// names. This mirrors the ordering used when canonicalizing shapes.
  pub fn compare_prop_keys(&self, a: &crate::PropKey, b: &crate::PropKey) -> Ordering {
    let names = self.names.read();
    a.cmp_with(b, &|id| names.name(id))
  }

  /// Deterministically compare two signatures using the same ordering applied
  /// when interning shapes and callable overload sets.
  pub fn compare_signatures(&self, a: SignatureId, b: SignatureId) -> Ordering {
    self.signature_cmp(a, b)
  }

  pub fn intern_type(&self, kind: TypeKind) -> TypeId {
    let kind = self.canonicalize_kind(kind);
    match kind {
      TypeKind::Union(members) => self.union(members),
      TypeKind::Intersection(members) => self.intersection(members),
      other => self.insert_type_direct(other),
    }
  }

  pub fn canon(&self, ty: TypeId) -> TypeId {
    match self.type_kind(ty) {
      TypeKind::Union(members) => self.union(members),
      TypeKind::Intersection(members) => self.intersection(members),
      _ => ty,
    }
  }

  fn canonicalize_kind(&self, kind: TypeKind) -> TypeKind {
    match kind {
      TypeKind::Union(members) => TypeKind::Union(members),
      TypeKind::Intersection(members) => TypeKind::Intersection(members),
      TypeKind::Array { ty, readonly } => TypeKind::Array {
        ty: self.canon(ty),
        readonly,
      },
      TypeKind::Tuple(mut elems) => {
        for elem in elems.iter_mut() {
          elem.ty = self.canon(elem.ty);
        }
        TypeKind::Tuple(elems)
      }
      TypeKind::Ref { def, args } => TypeKind::Ref {
        def,
        args: args.into_iter().map(|t| self.canon(t)).collect(),
      },
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => TypeKind::Conditional {
        check: self.canon(check),
        extends: self.canon(extends),
        true_ty: self.canon(true_ty),
        false_ty: self.canon(false_ty),
        distributive,
      },
      TypeKind::Infer { param, constraint } => TypeKind::Infer {
        param,
        constraint: constraint.map(|c| self.canon(c)),
      },
      TypeKind::Mapped(mut mapped) => {
        // Preserve mapped key source/value exactly as lowered to avoid widening
        // literal unions (e.g. `"a" | "b"`) into their primitive counterparts.
        // These are already deterministic from the lowering pipeline.
        if let Some(name) = mapped.name_type.as_mut() {
          *name = self.canon(*name);
        }
        if let Some(as_type) = mapped.as_type.as_mut() {
          *as_type = self.canon(*as_type);
        }
        TypeKind::Mapped(mapped)
      }
      TypeKind::TemplateLiteral(mut tpl) => {
        for span in tpl.spans.iter_mut() {
          span.ty = self.canon(span.ty);
        }
        TypeKind::TemplateLiteral(tpl)
      }
      TypeKind::Intrinsic { kind, ty } => TypeKind::Intrinsic {
        kind,
        ty: self.canon(ty),
      },
      TypeKind::IndexedAccess { obj, index } => TypeKind::IndexedAccess {
        obj: self.canon(obj),
        index: self.canon(index),
      },
      TypeKind::KeyOf(inner) => TypeKind::KeyOf(self.canon(inner)),
      TypeKind::Callable { mut overloads } => {
        Self::stable_dedup_signatures(&mut overloads);
        overloads.sort_by(|a, b| self.signature_cmp(*a, *b));
        TypeKind::Callable { overloads }
      }
      other => other,
    }
  }

  pub fn union(&self, members: Vec<TypeId>) -> TypeId {
    let mut flat = Vec::new();
    let mut has_unknown = false;
    for member in members.into_iter().map(|m| self.canon(m)) {
      match self.type_kind(member) {
        TypeKind::Any => return self.primitives.any,
        TypeKind::Unknown => {
          has_unknown = true;
        }
        TypeKind::Never => {}
        TypeKind::Union(inner) => flat.extend(inner),
        _ => flat.push(member),
      }
    }

    if has_unknown {
      return self.primitives.unknown;
    }

    let mut has_boolean = false;
    let mut has_number = false;
    let mut has_string = false;
    let mut has_bigint = false;
    let mut has_symbol = false;
    for member in &flat {
      match self.type_kind(*member) {
        TypeKind::Boolean => has_boolean = true,
        TypeKind::Number => has_number = true,
        TypeKind::String => has_string = true,
        TypeKind::BigInt => has_bigint = true,
        TypeKind::Symbol => has_symbol = true,
        _ => {}
      }
    }

    flat.retain(|member| match self.type_kind(*member) {
      TypeKind::BooleanLiteral(_) => !has_boolean,
      TypeKind::NumberLiteral(_) => !has_number,
      TypeKind::StringLiteral(_) => !has_string,
      TypeKind::TemplateLiteral(_) => !has_string,
      TypeKind::BigIntLiteral(_) => !has_bigint,
      TypeKind::UniqueSymbol => !has_symbol,
      _ => true,
    });

    self.sort_and_dedup(&mut flat);
    if flat.is_empty() {
      return self.primitives.never;
    }
    if flat.len() == 1 {
      return flat[0];
    }
    if flat.len() == 2
      && matches!(self.type_kind(flat[0]), TypeKind::BooleanLiteral(_))
      && matches!(self.type_kind(flat[1]), TypeKind::BooleanLiteral(_))
    {
      return self.primitives.boolean;
    }

    self.insert_type_direct(TypeKind::Union(flat))
  }

  pub fn intersection(&self, members: Vec<TypeId>) -> TypeId {
    let mut flat = Vec::new();
    let mut has_any = false;

    for member in members.into_iter().map(|m| self.canon(m)) {
      match self.type_kind(member) {
        TypeKind::Never => return self.primitives.never,
        TypeKind::Any => has_any = true,
        TypeKind::Unknown => {}
        TypeKind::Intersection(inner) => flat.extend(inner),
        _ => flat.push(member),
      }
    }

    if has_any {
      return self.primitives.any;
    }

    let mut has_boolean_literal = false;
    let mut has_number_literal = false;
    let mut has_string_literal = false;
    let mut has_bigint_literal = false;
    let mut has_template_literal = false;
    let mut has_unique_symbol = false;
    for member in &flat {
      match self.type_kind(*member) {
        TypeKind::BooleanLiteral(_) => has_boolean_literal = true,
        TypeKind::NumberLiteral(_) => has_number_literal = true,
        TypeKind::StringLiteral(_) => has_string_literal = true,
        TypeKind::BigIntLiteral(_) => has_bigint_literal = true,
        TypeKind::TemplateLiteral(_) => has_template_literal = true,
        TypeKind::UniqueSymbol => has_unique_symbol = true,
        _ => {}
      }
    }

    if has_boolean_literal {
      flat.retain(|member| !matches!(self.type_kind(*member), TypeKind::Boolean));
    }
    if has_number_literal {
      flat.retain(|member| !matches!(self.type_kind(*member), TypeKind::Number));
    }
    if has_string_literal {
      flat.retain(|member| !matches!(self.type_kind(*member), TypeKind::String));
    }
    if has_bigint_literal {
      flat.retain(|member| !matches!(self.type_kind(*member), TypeKind::BigInt));
    }
    if has_template_literal {
      flat.retain(|member| !matches!(self.type_kind(*member), TypeKind::String));
    }
    if has_unique_symbol {
      flat.retain(|member| !matches!(self.type_kind(*member), TypeKind::Symbol));
    }

    // unknown acts as identity; if no other members, it is the result.
    if flat.is_empty() {
      return self.primitives.unknown;
    }

    self.sort_and_dedup(&mut flat);
    if flat.len() == 1 {
      return flat[0];
    }

    const FAMILY_STRING: u8 = 1 << 0;
    const FAMILY_NUMBER: u8 = 1 << 1;
    const FAMILY_BOOLEAN: u8 = 1 << 2;
    const FAMILY_BIGINT: u8 = 1 << 3;
    const FAMILY_SYMBOL: u8 = 1 << 4;

    let mut families: u8 = 0;
    let mut bool_literal: Option<TypeId> = None;
    let mut number_literal: Option<TypeId> = None;
    let mut string_literal: Option<TypeId> = None;
    let mut bigint_literal: Option<TypeId> = None;
    for member in &flat {
      match self.type_kind(*member) {
        TypeKind::String => families |= FAMILY_STRING,
        TypeKind::StringLiteral(_) => {
          families |= FAMILY_STRING;
          if let Some(prev) = string_literal {
            if prev != *member {
              return self.primitives.never;
            }
          } else {
            string_literal = Some(*member);
          }
        }
        TypeKind::TemplateLiteral(_) => families |= FAMILY_STRING,
        TypeKind::Number => families |= FAMILY_NUMBER,
        TypeKind::NumberLiteral(_) => {
          families |= FAMILY_NUMBER;
          if let Some(prev) = number_literal {
            if prev != *member {
              return self.primitives.never;
            }
          } else {
            number_literal = Some(*member);
          }
        }
        TypeKind::Boolean => families |= FAMILY_BOOLEAN,
        TypeKind::BooleanLiteral(_) => {
          families |= FAMILY_BOOLEAN;
          if let Some(prev) = bool_literal {
            if prev != *member {
              return self.primitives.never;
            }
          } else {
            bool_literal = Some(*member);
          }
        }
        TypeKind::BigInt => families |= FAMILY_BIGINT,
        TypeKind::BigIntLiteral(_) => {
          families |= FAMILY_BIGINT;
          if let Some(prev) = bigint_literal {
            if prev != *member {
              return self.primitives.never;
            }
          } else {
            bigint_literal = Some(*member);
          }
        }
        TypeKind::Symbol | TypeKind::UniqueSymbol => families |= FAMILY_SYMBOL,
        _ => {}
      }

      if families & families.wrapping_sub(1) != 0 {
        return self.primitives.never;
      }
    }

    self.insert_type_direct(TypeKind::Intersection(flat))
  }

  fn sort_and_dedup(&self, members: &mut Vec<TypeId>) {
    members.sort_by(|a, b| self.type_cmp(*a, *b));
    members.dedup();
  }

  pub fn type_cmp(&self, a: TypeId, b: TypeId) -> Ordering {
    if a == b {
      return Ordering::Equal;
    }
    let a_kind = self.type_kind(a);
    let b_kind = self.type_kind(b);
    let discr = a_kind.discriminant().cmp(&b_kind.discriminant());
    if discr != Ordering::Equal {
      return discr;
    }
    let ord = match (a_kind, b_kind) {
      (TypeKind::BooleanLiteral(a), TypeKind::BooleanLiteral(b)) => a.cmp(&b),
      (TypeKind::NumberLiteral(a), TypeKind::NumberLiteral(b)) => a.cmp(&b),
      (TypeKind::StringLiteral(a), TypeKind::StringLiteral(b)) => {
        let names = self.names.read();
        names.name(a).cmp(names.name(b))
      }
      (TypeKind::BigIntLiteral(a), TypeKind::BigIntLiteral(b)) => a.cmp(&b),
      (TypeKind::Union(a), TypeKind::Union(b)) => {
        self.composite_cmp(CompositeKind::Union(&a), CompositeKind::Union(&b))
      }
      (TypeKind::Intersection(a), TypeKind::Intersection(b)) => self.composite_cmp(
        CompositeKind::Intersection(&a),
        CompositeKind::Intersection(&b),
      ),
      (TypeKind::Object(a), TypeKind::Object(b)) => {
        let a_shape = self.object(a).shape;
        let b_shape = self.object(b).shape;
        self.composite_cmp(
          CompositeKind::Object(&self.shape(a_shape)),
          CompositeKind::Object(&self.shape(b_shape)),
        )
      }
      (TypeKind::Callable { overloads: a }, TypeKind::Callable { overloads: b }) => {
        self.compare_signature_slices(&a, &b)
      }
      (
        TypeKind::Ref {
          def: a_def,
          args: a_args,
        },
        TypeKind::Ref {
          def: b_def,
          args: b_args,
        },
      ) => {
        let ord = a_def.0.cmp(&b_def.0);
        if ord != Ordering::Equal {
          return ord;
        }
        self.compare_slices(&a_args, &b_args)
      }
      (TypeKind::This, TypeKind::This) => Ordering::Equal,
      (
        TypeKind::Infer {
          param: a,
          constraint: a_c,
        },
        TypeKind::Infer {
          param: b,
          constraint: b_c,
        },
      ) => a.0.cmp(&b.0).then_with(|| self.option_type_cmp(a_c, b_c)),
      (TypeKind::Tuple(a), TypeKind::Tuple(b)) => {
        let mut idx = 0;
        loop {
          let Some(a_elem) = a.get(idx) else {
            break a.len().cmp(&b.len());
          };
          let Some(b_elem) = b.get(idx) else {
            break a.len().cmp(&b.len());
          };
          let ord = self
            .type_cmp(a_elem.ty, b_elem.ty)
            .then_with(|| a_elem.optional.cmp(&b_elem.optional))
            .then_with(|| a_elem.rest.cmp(&b_elem.rest))
            .then_with(|| a_elem.readonly.cmp(&b_elem.readonly));
          if ord != Ordering::Equal {
            break ord;
          }
          idx += 1;
        }
      }
      (
        TypeKind::Array {
          ty: a,
          readonly: ar,
        },
        TypeKind::Array {
          ty: b,
          readonly: br,
        },
      ) => ar.cmp(&br).then_with(|| self.type_cmp(a, b)),
      (TypeKind::TypeParam(a), TypeKind::TypeParam(b)) => a.0.cmp(&b.0),
      (
        TypeKind::Predicate {
          parameter: a_param,
          asserted: a_asserted,
          asserts: a_asserts,
        },
        TypeKind::Predicate {
          parameter: b_param,
          asserted: b_asserted,
          asserts: b_asserts,
        },
      ) => a_param
        .cmp(&b_param)
        .then_with(|| self.option_type_cmp(a_asserted, b_asserted))
        .then_with(|| a_asserts.cmp(&b_asserts)),
      (
        TypeKind::Conditional {
          check: a_c,
          extends: a_e,
          true_ty: a_t,
          false_ty: a_f,
          distributive: a_d,
        },
        TypeKind::Conditional {
          check: b_c,
          extends: b_e,
          true_ty: b_t,
          false_ty: b_f,
          distributive: b_d,
        },
      ) => self
        .type_cmp(a_c, b_c)
        .then_with(|| self.type_cmp(a_e, b_e))
        .then_with(|| self.type_cmp(a_t, b_t))
        .then_with(|| self.type_cmp(a_f, b_f))
        .then_with(|| a_d.cmp(&b_d)),
      (TypeKind::Mapped(a), TypeKind::Mapped(b)) => a
        .param
        .0
        .cmp(&b.param.0)
        .then_with(|| self.type_cmp(a.source, b.source))
        .then_with(|| self.type_cmp(a.value, b.value))
        .then_with(|| a.readonly.cmp(&b.readonly))
        .then_with(|| a.optional.cmp(&b.optional))
        .then_with(|| self.option_type_cmp(a.name_type, b.name_type))
        .then_with(|| self.option_type_cmp(a.as_type, b.as_type)),
      (TypeKind::TemplateLiteral(a), TypeKind::TemplateLiteral(b)) => {
        a.head.cmp(&b.head).then_with(|| {
          let mut idx = 0;
          loop {
            let Some(left) = a.spans.get(idx) else {
              return a.spans.len().cmp(&b.spans.len());
            };
            let Some(right) = b.spans.get(idx) else {
              return a.spans.len().cmp(&b.spans.len());
            };
            let ord = self
              .type_cmp(left.ty, right.ty)
              .then_with(|| left.literal.cmp(&right.literal));
            if ord != Ordering::Equal {
              return ord;
            }
            idx += 1;
          }
        })
      }
      (TypeKind::Intrinsic { kind: a_k, ty: a_t }, TypeKind::Intrinsic { kind: b_k, ty: b_t }) => {
        a_k.cmp(&b_k).then_with(|| self.type_cmp(a_t, b_t))
      }
      (
        TypeKind::IndexedAccess {
          obj: a_o,
          index: a_i,
        },
        TypeKind::IndexedAccess {
          obj: b_o,
          index: b_i,
        },
      ) => self
        .type_cmp(a_o, b_o)
        .then_with(|| self.type_cmp(a_i, b_i)),
      (TypeKind::KeyOf(a), TypeKind::KeyOf(b)) => self.type_cmp(a, b),
      _ => Ordering::Equal,
    };
    ord.then_with(|| a.0.cmp(&b.0))
  }

  fn signature_cmp(&self, a: SignatureId, b: SignatureId) -> Ordering {
    if a == b {
      return Ordering::Equal;
    }
    let a_sig = self.signature(a);
    let b_sig = self.signature(b);
    self
      .compare_params(&a_sig.params, &b_sig.params)
      .then_with(|| self.type_cmp(a_sig.ret, b_sig.ret))
      .then_with(|| self.compare_type_params(&a_sig.type_params, &b_sig.type_params))
      .then_with(|| self.option_type_cmp(a_sig.this_param, b_sig.this_param))
      .then_with(|| a.cmp(&b))
  }

  fn compare_params(&self, a: &[Param], b: &[Param]) -> Ordering {
    let mut idx = 0;
    loop {
      let Some(a_param) = a.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let Some(b_param) = b.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let ord = a_param
        .optional
        .cmp(&b_param.optional)
        .then_with(|| a_param.rest.cmp(&b_param.rest))
        .then_with(|| self.type_cmp(a_param.ty, b_param.ty));
      if ord != Ordering::Equal {
        return ord;
      }
      idx += 1;
    }
  }

  fn compare_type_params(&self, a: &[TypeParamDecl], b: &[TypeParamDecl]) -> Ordering {
    let mut idx = 0;
    loop {
      let Some(a_param) = a.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let Some(b_param) = b.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let ord = a_param
        .id
        .cmp(&b_param.id)
        .then_with(|| self.option_type_cmp(a_param.constraint, b_param.constraint))
        .then_with(|| self.option_type_cmp(a_param.default, b_param.default));
      if ord != Ordering::Equal {
        return ord;
      }
      idx += 1;
    }
  }

  fn option_type_cmp(&self, a: Option<TypeId>, b: Option<TypeId>) -> Ordering {
    match (a, b) {
      (Some(a), Some(b)) => self.type_cmp(a, b),
      (None, None) => Ordering::Equal,
      (Some(_), None) => Ordering::Greater,
      (None, Some(_)) => Ordering::Less,
    }
  }

  fn composite_cmp(&self, a: CompositeKind<'_>, b: CompositeKind<'_>) -> Ordering {
    match (a, b) {
      (CompositeKind::Union(a), CompositeKind::Union(b))
      | (CompositeKind::Intersection(a), CompositeKind::Intersection(b)) => {
        self.compare_slices(a, b)
      }
      (CompositeKind::Object(a), CompositeKind::Object(b)) => {
        let mut idx = 0;
        loop {
          let Some(a_prop) = a.properties.get(idx) else {
            return a
              .properties
              .len()
              .cmp(&b.properties.len())
              .then_with(|| self.compare_signature_slices(&a.call_signatures, &b.call_signatures))
              .then_with(|| {
                self.compare_signature_slices(&a.construct_signatures, &b.construct_signatures)
              })
              .then_with(|| self.compare_indexers(&a.indexers, &b.indexers));
          };
          let Some(b_prop) = b.properties.get(idx) else {
            return a
              .properties
              .len()
              .cmp(&b.properties.len())
              .then_with(|| self.compare_signature_slices(&a.call_signatures, &b.call_signatures))
              .then_with(|| {
                self.compare_signature_slices(&a.construct_signatures, &b.construct_signatures)
              })
              .then_with(|| self.compare_indexers(&a.indexers, &b.indexers));
          };
          let ord = self.compare_props(a_prop, b_prop);
          if ord != Ordering::Equal {
            return ord;
          }
          idx += 1;
        }
      }
      _ => Ordering::Equal,
    }
  }

  fn compare_props(&self, a: &Property, b: &Property) -> Ordering {
    let names = self.names.read();
    let ord = a.key.cmp_with(&b.key, &|id| names.name(id));
    if ord != Ordering::Equal {
      return ord;
    }
    self
      .type_cmp(a.data.ty, b.data.ty)
      .then_with(|| a.data.optional.cmp(&b.data.optional))
      .then_with(|| a.data.readonly.cmp(&b.data.readonly))
      .then_with(|| a.data.is_method.cmp(&b.data.is_method))
      .then_with(|| a.data.accessibility.cmp(&b.data.accessibility))
      .then_with(|| a.data.declared_on.cmp(&b.data.declared_on))
  }

  fn compare_indexers(&self, a: &[Indexer], b: &[Indexer]) -> Ordering {
    let mut idx = 0;
    loop {
      let Some(ai) = a.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let Some(bi) = b.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let ord = self
        .type_cmp(ai.key_type, bi.key_type)
        .then_with(|| self.type_cmp(ai.value_type, bi.value_type))
        .then_with(|| ai.readonly.cmp(&bi.readonly));
      if ord != Ordering::Equal {
        return ord;
      }
      idx += 1;
    }
  }

  fn compare_signature_slices(&self, a: &[SignatureId], b: &[SignatureId]) -> Ordering {
    let mut idx = 0;
    loop {
      let Some(asig) = a.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let Some(bsig) = b.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let ord = self.signature_cmp(*asig, *bsig);
      if ord != Ordering::Equal {
        return ord;
      }
      idx += 1;
    }
  }

  fn compare_slices(&self, a: &[TypeId], b: &[TypeId]) -> Ordering {
    let mut idx = 0;
    loop {
      let Some(at) = a.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let Some(bt) = b.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let ord = self.type_cmp(*at, *bt);
      if ord != Ordering::Equal {
        return ord;
      }
      idx += 1;
    }
  }

  pub fn display<'a>(&'a self, ty: TypeId) -> TypeDisplay<'a> {
    TypeDisplay::new(self, ty)
  }

  /// Evaluate complex type operators into concrete types.
  ///
  /// This uses a no-op [`crate::TypeExpander`], meaning `TypeKind::Ref` nodes
  /// are left unexpanded.
  pub fn evaluate(self: &Arc<Self>, ty: TypeId) -> TypeId {
    struct NoopExpander;

    impl crate::TypeExpander for NoopExpander {
      fn expand(
        &self,
        _store: &TypeStore,
        _def: crate::DefId,
        _args: &[TypeId],
      ) -> Option<crate::ExpandedType> {
        None
      }
    }

    let expander = NoopExpander;
    let mut evaluator = crate::TypeEvaluator::new(Arc::clone(self), &expander);
    evaluator.evaluate(ty)
  }

  /// Export a stable JSON representation of a type. This is intentionally
  /// shallow (referencing nested types by ID) to avoid infinite recursion
  /// while still providing a deterministic shape for comparisons.
  #[cfg(feature = "serde-json")]
  pub fn debug_json(&self, ty: TypeId) -> serde_json::Value {
    use serde_json::json;
    match self.type_kind(ty) {
      TypeKind::Any => json!({ "kind": "any" }),
      TypeKind::Unknown => json!({ "kind": "unknown" }),
      TypeKind::Never => json!({ "kind": "never" }),
      TypeKind::Void => json!({ "kind": "void" }),
      TypeKind::Null => json!({ "kind": "null" }),
      TypeKind::Undefined => json!({ "kind": "undefined" }),
      TypeKind::EmptyObject => json!({ "kind": "empty_object" }),
      TypeKind::Boolean => json!({ "kind": "boolean" }),
      TypeKind::Number => json!({ "kind": "number" }),
      TypeKind::String => json!({ "kind": "string" }),
      TypeKind::BigInt => json!({ "kind": "bigint" }),
      TypeKind::Symbol => json!({ "kind": "symbol" }),
      TypeKind::UniqueSymbol => json!({ "kind": "unique_symbol" }),
      TypeKind::BooleanLiteral(v) => json!({ "kind": "bool_lit", "value": v }),
      TypeKind::NumberLiteral(v) => json!({ "kind": "num_lit", "value": v }),
      TypeKind::StringLiteral(id) => json!({ "kind": "str_lit", "value": self.name(id) }),
      TypeKind::BigIntLiteral(v) => json!({ "kind": "bigint_lit", "value": v.to_string() }),
      TypeKind::Union(members) => {
        json!({ "kind": "union", "members": members.iter().map(|m| m.0.to_string()).collect::<Vec<_>>() })
      }
      TypeKind::Intersection(members) => {
        json!({ "kind": "intersection", "members": members.iter().map(|m| m.0.to_string()).collect::<Vec<_>>() })
      }
      TypeKind::Object(obj) => {
        let shape = self.object(obj).shape;
        json!({ "kind": "object", "shape": shape.0.to_string() })
      }
      TypeKind::Callable { overloads } => {
        json!({ "kind": "callable", "overloads": overloads.iter().map(|o| o.0.to_string()).collect::<Vec<_>>() })
      }
      TypeKind::Ref { def, args } => {
        json!({ "kind": "ref", "def": def.0, "args": args.iter().map(|a| a.0.to_string()).collect::<Vec<_>>() })
      }
      TypeKind::This => json!({ "kind": "this" }),
      TypeKind::Infer { param, constraint } => json!({
        "kind": "infer",
        "param": param.0,
        "constraint": constraint.map(|c| c.0.to_string()),
      }),
      TypeKind::Tuple(elems) => json!({
        "kind": "tuple",
        "elems": elems.iter().map(|e| json!({
          "ty": e.ty.0.to_string(),
          "optional": e.optional,
          "rest": e.rest,
          "readonly": e.readonly,
        })).collect::<Vec<_>>(),
      }),
      TypeKind::Array { ty, readonly } => {
        json!({ "kind": "array", "ty": ty.0.to_string(), "readonly": readonly })
      }
      TypeKind::TypeParam(id) => json!({ "kind": "type_param", "id": id.0 }),
      TypeKind::Predicate {
        asserted, asserts, ..
      } => json!({
        "kind": "predicate",
        "asserted": asserted.map(|t| t.0.to_string()),
        "asserts": asserts,
      }),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => json!({
        "kind": "conditional",
        "check": check.0.to_string(),
        "extends": extends.0.to_string(),
        "true": true_ty.0.to_string(),
        "false": false_ty.0.to_string(),
        "distributive": distributive,
      }),
      TypeKind::Mapped(mapped) => json!({
        "kind": "mapped",
        "param": mapped.param.0,
        "source": mapped.source.0.to_string(),
        "value": mapped.value.0.to_string(),
        "readonly": format!("{:?}", mapped.readonly),
        "optional": format!("{:?}", mapped.optional),
        "name_type": mapped.name_type.map(|t| t.0.to_string()),
        "as_type": mapped.as_type.map(|t| t.0.to_string()),
      }),
      TypeKind::TemplateLiteral(tpl) => json!({
        "kind": "template",
        "head": tpl.head,
        "spans": tpl.spans.iter().map(|s| json!({"literal": s.literal, "ty": s.ty.0.to_string()})).collect::<Vec<_>>()
      }),
      TypeKind::IndexedAccess { obj, index } => {
        json!({ "kind": "indexed", "obj": obj.0.to_string(), "index": index.0.to_string() })
      }
      TypeKind::KeyOf(inner) => json!({ "kind": "keyof", "ty": inner.0.to_string() }),
      TypeKind::Intrinsic { kind, ty } => json!({
        "kind": "intrinsic",
        "name": kind.as_str(),
        "ty": ty.0.to_string()
      }),
    }
  }
}

#[cfg(feature = "serde")]
impl Serialize for TypeStore {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    self.snapshot().serialize(serializer)
  }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for TypeStore {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    let snapshot = TypeStoreSnapshot::deserialize(deserializer)?;
    Ok(Self::from_snapshot_inner(snapshot))
  }
}

#[cfg(all(test, not(feature = "strict-determinism")))]
mod tests {
  use super::*;
  use ordered_float::OrderedFloat;
  use std::collections::HashSet;
  use std::sync::{Arc, Barrier};
  use std::thread;

  fn colliding_fingerprint(_: u128, domain: u64, salt: u64) -> u128 {
    ((domain as u128) << 64) | salt as u128
  }

  #[test]
  #[cfg(not(feature = "strict-determinism"))]
  fn deterministic_rehash_on_collisions() {
    let store =
      TypeStore::with_options_and_fingerprint(TypeOptions::default(), colliding_fingerprint);
    let primitives = store.primitive_ids();

    let sig_a = store.intern_signature(Signature::new(
      vec![Param {
        name: None,
        ty: primitives.boolean,
        optional: false,
        rest: false,
      }],
      primitives.number,
    ));
    let sig_b = store.intern_signature(Signature::new(
      vec![Param {
        name: None,
        ty: primitives.string,
        optional: true,
        rest: false,
      }],
      primitives.boolean,
    ));
    assert_ne!(sig_a, sig_b);
    assert_eq!(store.signature(sig_a).ret, primitives.number);
    assert_eq!(store.signature(sig_b).ret, primitives.boolean);

    let mut shape_a = Shape::new();
    shape_a.call_signatures.push(sig_a);
    let mut shape_b = Shape::new();
    shape_b.call_signatures.push(sig_b);

    let shape_a = store.intern_shape(shape_a);
    let shape_b = store.intern_shape(shape_b);
    assert_ne!(shape_a, shape_b);
    assert_eq!(store.shape(shape_a).call_signatures, vec![sig_a]);
    assert_eq!(store.shape(shape_b).call_signatures, vec![sig_b]);

    let object_a = store.intern_object(ObjectType { shape: shape_a });
    let object_b = store.intern_object(ObjectType { shape: shape_b });
    assert_ne!(object_a, object_b);
    assert_eq!(store.object(object_a).shape, shape_a);
    assert_eq!(store.object(object_b).shape, shape_b);

    let type_a = store.intern_type(TypeKind::Object(object_a));
    let type_b = store.intern_type(TypeKind::Object(object_b));

    assert_ne!(type_a, type_b);
    assert_eq!(store.type_kind(type_a), TypeKind::Object(object_a));
    assert_eq!(store.type_kind(type_b), TypeKind::Object(object_b));

    let repeated = vec![
      store.intern_signature(Signature::new(Vec::new(), primitives.number)),
      store.intern_signature(Signature::new(Vec::new(), primitives.number)),
    ];
    assert_eq!(repeated[0], repeated[1]);

    let ids: HashSet<_> = [type_a, type_b].into_iter().collect();
    assert_eq!(ids.len(), 2);

    let shapes: HashSet<_> = [shape_a, shape_b].into_iter().collect();
    assert_eq!(shapes.len(), 2);

    let objects: HashSet<_> = [object_a, object_b].into_iter().collect();
    assert_eq!(objects.len(), 2);
  }

  #[test]
  #[cfg(not(feature = "strict-determinism"))]
  fn parallel_interning_retries_collisions() {
    let store =
      TypeStore::with_options_and_fingerprint(TypeOptions::default(), colliding_fingerprint);
    let name = store.intern_name("parallel");

    let kinds = vec![
      TypeKind::BooleanLiteral(true),
      TypeKind::NumberLiteral(OrderedFloat(1.0)),
      TypeKind::StringLiteral(name),
    ];

    let barrier = Arc::new(Barrier::new(4));
    let handles: Vec<_> = (0..4)
      .map(|_| {
        let store = Arc::clone(&store);
        let barrier = barrier.clone();
        let kinds = kinds.clone();
        thread::spawn(move || {
          barrier.wait();
          kinds
            .iter()
            .map(|kind| store.intern_type(kind.clone()))
            .collect::<Vec<_>>()
        })
      })
      .collect();

    let mut results = Vec::new();
    for handle in handles {
      results.push(handle.join().expect("thread panicked"));
    }

    let reference = results.first().expect("no thread results").clone();
    for ids in results.iter().skip(1) {
      assert_eq!(ids, &reference);
    }

    for (id, expected_kind) in reference.iter().zip(kinds.iter()) {
      assert_eq!(store.type_kind(*id), expected_kind.clone());
    }
  }
}
