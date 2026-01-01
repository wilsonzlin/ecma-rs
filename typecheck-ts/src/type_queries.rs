use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use types_ts_interned::{
  Accessibility, DefId, EvaluatorCaches, Indexer, PropKey, Signature, SignatureId, TypeEvaluator,
  TypeExpander, TypeId, TypeKind, TypeParamId, TypeStore,
};

/// Summary of a type's top-level shape without exposing the full `TypeKind`
/// enum. This is intentionally coarse to keep the public API stable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeKindSummary {
  Any,
  Unknown,
  Never,
  Void,
  Null,
  Undefined,
  EmptyObject,
  Boolean,
  Number,
  String,
  BigInt,
  Symbol,
  UniqueSymbol,
  Predicate,
  BooleanLiteral(bool),
  NumberLiteral(OrderedFloat<f64>),
  StringLiteral(String),
  BigIntLiteral(BigInt),
  This,
  Infer(TypeParamId),
  Tuple { len: usize },
  Array { readonly: bool },
  Union { members: usize },
  Intersection { members: usize },
  Object,
  Callable { overloads: usize },
  Ref { def: DefId, args: usize },
  TypeParam(TypeParamId),
  Conditional,
  Mapped,
  TemplateLiteral,
  IndexedAccess,
  KeyOf,
}

/// Key for an object property.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropertyKey {
  String(String),
  Number(i64),
  Symbol(String),
}

/// Information about a single property on a type after merging unions or
/// intersections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyInfo {
  pub key: PropertyKey,
  pub ty: TypeId,
  pub optional: bool,
  pub readonly: bool,
  pub accessibility: Option<Accessibility>,
  pub is_method: bool,
}

/// Information about a callable or construct signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureInfo {
  pub id: SignatureId,
  pub signature: Signature,
}

/// Information about an index signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexerInfo {
  pub key_type: TypeId,
  pub value_type: TypeId,
  pub readonly: bool,
}

/// Deterministic structural queries for `types-ts-interned` types. The
/// `TypeExpander` is used to lazily expand `TypeKind::Ref` nodes with recursion
/// guards handled by [`TypeEvaluator`].
pub struct TypeQueries<'a, E: TypeExpander> {
  store: Arc<TypeStore>,
  expander: &'a E,
  caches: Option<EvaluatorCaches>,
}

impl<'a, E: TypeExpander> TypeQueries<'a, E> {
  pub fn new(store: Arc<TypeStore>, expander: &'a E) -> Self {
    Self {
      store,
      expander,
      caches: None,
    }
  }

  /// Construct queries backed by externally managed evaluator caches. When
  /// shared caches are provided, successive calls will reuse the same cache
  /// shards and maintain bounded memory according to the caller's cache
  /// configuration.
  pub fn with_caches(store: Arc<TypeStore>, expander: &'a E, caches: EvaluatorCaches) -> Self {
    Self {
      store,
      expander,
      caches: Some(caches),
    }
  }

  fn with_ctx<R>(&self, f: impl FnOnce(&mut QueryCtx<'_, E>) -> R) -> R {
    let mut ctx = QueryCtx::new(Arc::clone(&self.store), self.expander, self.caches.clone());
    f(&mut ctx)
  }

  /// Summary of the given type after lazy expansion.
  pub fn type_kind(&self, ty: TypeId) -> TypeKindSummary {
    self.with_ctx(|ctx| ctx.summarize_kind(ty))
  }

  /// Lazily expand the given type reference using the configured expander.
  /// Returned [`TypeId`]s are interned in the same [`TypeStore`] and can be
  /// inspected directly.
  pub fn evaluate(&self, ty: TypeId) -> TypeId {
    self.with_ctx(|ctx| ctx.evaluate(ty))
  }

  /// Deterministic list of properties on the given type. For union types, only
  /// properties present on all members are returned. For intersection types,
  /// properties from all members are merged. Property types include `undefined`
  /// when the property is optional in any contributing type.
  pub fn properties_of(&self, ty: TypeId) -> Vec<PropertyInfo> {
    self.with_ctx(|ctx| {
      let shape = ctx.shape_for(ty);
      shape
        .props
        .into_iter()
        .map(|prop| {
          let ty = effective_type(&prop, &ctx.store);
          PropertyInfo {
            key: prop_key_to_public(&prop.key, &ctx.store),
            ty,
            optional: !prop.required,
            readonly: prop.readonly,
            accessibility: prop.accessibility,
            is_method: prop.is_method,
          }
        })
        .collect()
    })
  }

  /// Type of a specific property, if it exists on the given type. Returns
  /// `None` for properties that are not present on all union constituents. For
  /// intersection types, properties from any member are considered with types
  /// intersected.
  pub fn property_type(&self, ty: TypeId, key: PropertyKey) -> Option<TypeId> {
    self.with_ctx(|ctx| {
      let shape = ctx.shape_for(ty);
      let internal = property_key_to_internal(&key, &ctx.store);
      shape
        .props
        .iter()
        .find(|prop| prop.key == internal)
        .map(|prop| effective_type(prop, &ctx.store))
        .or_else(|| {
          shape.indexers.iter().find_map(|idx| {
            if indexer_matches(&internal, idx, &ctx.store) {
              Some(idx.value_type)
            } else {
              None
            }
          })
        })
    })
  }

  /// Call signatures for the given type. Union types only expose signatures
  /// that are present on all constituents; intersection types accumulate
  /// signatures from all members (similar to overload merging).
  pub fn call_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    self.with_ctx(|ctx| {
      let shape = ctx.shape_for(ty);
      shape
        .call_sigs
        .into_iter()
        .map(|id| SignatureInfo {
          signature: ctx.store.signature(id),
          id,
        })
        .collect()
    })
  }

  /// Construct signatures for the given type. Union and intersection semantics
  /// mirror [`TypeQueries::call_signatures`].
  pub fn construct_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    self.with_ctx(|ctx| {
      let shape = ctx.shape_for(ty);
      shape
        .construct_sigs
        .into_iter()
        .map(|id| SignatureInfo {
          signature: ctx.store.signature(id),
          id,
        })
        .collect()
    })
  }

  /// Index signatures on the given type. Union types return indexers that are
  /// present on all constituents; intersection types merge indexers by key
  /// type, intersecting their value types.
  pub fn indexers(&self, ty: TypeId) -> Vec<IndexerInfo> {
    self.with_ctx(|ctx| {
      let mut indexers: Vec<_> = ctx
        .shape_for(ty)
        .indexers
        .into_iter()
        .map(|idx| IndexerInfo {
          key_type: idx.key_type,
          value_type: idx.value_type,
          readonly: idx.readonly,
        })
        .collect();
      sort_indexers(&mut indexers, &ctx.store);
      indexers
    })
  }
}

#[derive(Clone, Debug)]
struct PropertyEntry {
  key: PropKey,
  ty: TypeId,
  required: bool,
  type_optional: bool,
  readonly: bool,
  accessibility: Option<Accessibility>,
  is_method: bool,
}

#[derive(Clone, Debug, Default)]
struct ShapeInfo {
  props: Vec<PropertyEntry>,
  call_sigs: Vec<SignatureId>,
  construct_sigs: Vec<SignatureId>,
  indexers: Vec<Indexer>,
}

struct QueryCtx<'a, E: TypeExpander> {
  store: Arc<TypeStore>,
  evaluator: TypeEvaluator<'a, E>,
  shapes: HashMap<TypeId, ShapeInfo>,
  computing: HashSet<TypeId>,
}

impl<'a, E: TypeExpander> QueryCtx<'a, E> {
  fn new(store: Arc<TypeStore>, expander: &'a E, caches: Option<EvaluatorCaches>) -> Self {
    let evaluator = match caches {
      Some(caches) => TypeEvaluator::with_caches(Arc::clone(&store), expander, caches),
      None => TypeEvaluator::new(Arc::clone(&store), expander),
    };
    Self {
      evaluator,
      store,
      shapes: HashMap::new(),
      computing: HashSet::new(),
    }
  }

  fn summarize_kind(&mut self, ty: TypeId) -> TypeKindSummary {
    let evaluated = self.evaluator.evaluate(ty);
    summarize_kind(&self.store, evaluated)
  }

  fn evaluate(&mut self, ty: TypeId) -> TypeId {
    self.evaluator.evaluate(ty)
  }

  fn shape_for(&mut self, ty: TypeId) -> ShapeInfo {
    let evaluated = self.evaluator.evaluate(ty);
    if let Some(existing) = self.shapes.get(&evaluated) {
      return existing.clone();
    }
    if !self.computing.insert(evaluated) {
      return ShapeInfo::default();
    }

    let shape = match self.store.type_kind(evaluated) {
      TypeKind::Object(obj) => self.shape_from_object(obj),
      TypeKind::Callable { overloads } => {
        let mut call_sigs = overloads;
        sort_signatures(&mut call_sigs, &self.store);
        ShapeInfo {
          call_sigs,
          ..Default::default()
        }
      }
      TypeKind::Array { ty, readonly } => {
        let length_key = PropKey::String(self.store.intern_name("length".to_string()));
        let prim = self.store.primitive_ids();
        let mut props = vec![PropertyEntry {
          key: length_key,
          ty: prim.number,
          required: true,
          type_optional: false,
          readonly,
          accessibility: None,
          is_method: false,
        }];
        sort_properties(&mut props, &self.store);
        let mut indexers = vec![Indexer {
          key_type: prim.number,
          value_type: ty,
          readonly,
        }];
        sort_indexers(&mut indexers, &self.store);
        ShapeInfo {
          props,
          indexers,
          ..Default::default()
        }
      }
      TypeKind::Union(members) => self.shape_union(members),
      TypeKind::Intersection(members) => self.shape_intersection(members),
      _ => ShapeInfo::default(),
    };

    self.computing.remove(&evaluated);
    self.shapes.insert(evaluated, shape.clone());
    shape
  }

  fn shape_from_object(&self, obj: types_ts_interned::ObjectId) -> ShapeInfo {
    let object = self.store.object(obj);
    let shape = self.store.shape(object.shape);
    let mut props: Vec<PropertyEntry> = shape
      .properties
      .into_iter()
      .map(|prop| PropertyEntry {
        key: prop.key,
        ty: prop.data.ty,
        required: !prop.data.optional,
        type_optional: prop.data.optional,
        readonly: prop.data.readonly,
        accessibility: prop.data.accessibility,
        is_method: prop.data.is_method,
      })
      .collect();
    sort_properties(&mut props, &self.store);
    let mut call_sigs = shape.call_signatures;
    sort_signatures(&mut call_sigs, &self.store);
    let mut construct_sigs = shape.construct_signatures;
    sort_signatures(&mut construct_sigs, &self.store);
    let mut indexers = shape.indexers;
    sort_indexers(&mut indexers, &self.store);
    ShapeInfo {
      props,
      call_sigs,
      construct_sigs,
      indexers,
    }
  }

  fn shape_union(&mut self, members: Vec<TypeId>) -> ShapeInfo {
    if members.is_empty() {
      return ShapeInfo::default();
    }
    let shapes: Vec<_> = members.into_iter().map(|m| self.shape_for(m)).collect();
    let mut props = merge_union_properties(&shapes, &self.store);
    sort_properties(&mut props, &self.store);
    let mut call_sigs = intersect_signatures(&shapes, &self.store, |s| &s.call_sigs);
    sort_signatures(&mut call_sigs, &self.store);
    let mut construct_sigs = intersect_signatures(&shapes, &self.store, |s| &s.construct_sigs);
    sort_signatures(&mut construct_sigs, &self.store);
    let mut indexers = intersect_indexers(&shapes, &self.store);
    sort_indexers(&mut indexers, &self.store);

    ShapeInfo {
      props,
      call_sigs,
      construct_sigs,
      indexers,
    }
  }

  fn shape_intersection(&mut self, members: Vec<TypeId>) -> ShapeInfo {
    if members.is_empty() {
      return ShapeInfo::default();
    }
    let shapes: Vec<_> = members.into_iter().map(|m| self.shape_for(m)).collect();
    let mut props = merge_intersection_properties(&shapes, &self.store);
    sort_properties(&mut props, &self.store);
    let mut call_sigs = union_signatures(&shapes, &self.store, |s| &s.call_sigs);
    sort_signatures(&mut call_sigs, &self.store);
    let mut construct_sigs = union_signatures(&shapes, &self.store, |s| &s.construct_sigs);
    sort_signatures(&mut construct_sigs, &self.store);
    let mut indexers = union_indexers(&shapes, &self.store);
    sort_indexers(&mut indexers, &self.store);

    ShapeInfo {
      props,
      call_sigs,
      construct_sigs,
      indexers,
    }
  }
}

fn summarize_kind(store: &TypeStore, ty: TypeId) -> TypeKindSummary {
  match store.type_kind(ty) {
    TypeKind::Any => TypeKindSummary::Any,
    TypeKind::Unknown => TypeKindSummary::Unknown,
    TypeKind::Never => TypeKindSummary::Never,
    TypeKind::Void => TypeKindSummary::Void,
    TypeKind::Null => TypeKindSummary::Null,
    TypeKind::Undefined => TypeKindSummary::Undefined,
    TypeKind::EmptyObject => TypeKindSummary::EmptyObject,
    TypeKind::Boolean => TypeKindSummary::Boolean,
    TypeKind::Number => TypeKindSummary::Number,
    TypeKind::String => TypeKindSummary::String,
    TypeKind::BigInt => TypeKindSummary::BigInt,
    TypeKind::Symbol => TypeKindSummary::Symbol,
    TypeKind::UniqueSymbol => TypeKindSummary::UniqueSymbol,
    TypeKind::BooleanLiteral(val) => TypeKindSummary::BooleanLiteral(val),
    TypeKind::NumberLiteral(val) => TypeKindSummary::NumberLiteral(val),
    TypeKind::StringLiteral(id) => TypeKindSummary::StringLiteral(store.name(id)),
    TypeKind::BigIntLiteral(val) => TypeKindSummary::BigIntLiteral(val),
    TypeKind::This => TypeKindSummary::This,
    TypeKind::Infer { param, .. } => TypeKindSummary::Infer(param),
    TypeKind::Tuple(elems) => TypeKindSummary::Tuple { len: elems.len() },
    TypeKind::Array { readonly, .. } => TypeKindSummary::Array { readonly },
    TypeKind::Union(members) => TypeKindSummary::Union {
      members: members.len(),
    },
    TypeKind::Intersection(members) => TypeKindSummary::Intersection {
      members: members.len(),
    },
    TypeKind::Object(_) => TypeKindSummary::Object,
    TypeKind::Callable { overloads } => TypeKindSummary::Callable {
      overloads: overloads.len(),
    },
    TypeKind::Predicate { .. } => TypeKindSummary::Predicate,
    TypeKind::Ref { def, args } => TypeKindSummary::Ref {
      def,
      args: args.len(),
    },
    TypeKind::TypeParam(param) => TypeKindSummary::TypeParam(param),
    TypeKind::Conditional { .. } => TypeKindSummary::Conditional,
    TypeKind::Mapped(_) => TypeKindSummary::Mapped,
    TypeKind::TemplateLiteral(_) => TypeKindSummary::TemplateLiteral,
    TypeKind::IndexedAccess { .. } => TypeKindSummary::IndexedAccess,
    TypeKind::KeyOf(_) => TypeKindSummary::KeyOf,
  }
}

fn property_key_to_internal(key: &PropertyKey, store: &TypeStore) -> PropKey {
  match key {
    PropertyKey::String(s) => PropKey::String(store.intern_name(s.clone())),
    PropertyKey::Number(num) => PropKey::Number(*num),
    PropertyKey::Symbol(s) => PropKey::Symbol(store.intern_name(s.clone())),
  }
}

fn prop_key_to_public(key: &PropKey, store: &TypeStore) -> PropertyKey {
  match key {
    PropKey::String(id) => PropertyKey::String(store.name(*id)),
    PropKey::Number(num) => PropertyKey::Number(*num),
    PropKey::Symbol(id) => PropertyKey::Symbol(store.name(*id)),
  }
}

fn merge_union_properties(shapes: &[ShapeInfo], store: &TypeStore) -> Vec<PropertyEntry> {
  let mut keys: Vec<PropKey> = shapes
    .iter()
    .flat_map(|s| s.props.iter().map(|p| p.key.clone()))
    .collect();
  keys.sort_by(|a, b| store.compare_prop_keys(a, b));
  keys.dedup();

  let mut props = Vec::new();
  for key in keys.into_iter() {
    let mut merged_ty: Option<TypeId> = None;
    let mut all_required = true;
    let mut type_optional = false;
    let mut readonly = false;
    let mut accessibility: Option<Accessibility> = None;
    let mut is_method = false;

    let mut present = true;
    for shape in shapes {
      let Some(prop) = find_property(shape, &key, store) else {
        present = false;
        break;
      };
      merged_ty = Some(match merged_ty {
        Some(current) => store.union(vec![current, prop.ty]),
        None => prop.ty,
      });
      all_required &= prop.required;
      type_optional |= prop.type_optional;
      readonly |= prop.readonly;
      accessibility = merge_union_accessibility(accessibility, prop.accessibility);
      is_method |= prop.is_method;
    }

    if present {
      let ty = merged_ty.expect("union member provided property type");
      props.push(PropertyEntry {
        key,
        ty,
        required: all_required,
        type_optional,
        readonly,
        accessibility,
        is_method,
      });
    }
  }

  props
}

fn merge_intersection_properties(shapes: &[ShapeInfo], store: &TypeStore) -> Vec<PropertyEntry> {
  let mut keys: Vec<PropKey> = shapes
    .iter()
    .flat_map(|s| s.props.iter().map(|p| p.key.clone()))
    .collect();
  keys.sort_by(|a, b| store.compare_prop_keys(a, b));
  keys.dedup();

  let mut props = Vec::new();
  for key in keys.into_iter() {
    let mut merged_ty: Option<TypeId> = None;
    let mut required = false;
    let mut type_optional = false;
    let mut readonly = false;
    let mut accessibility: Option<Accessibility> = None;
    let mut is_method = false;

    for shape in shapes {
      if let Some(prop) = find_property(shape, &key, store) {
        merged_ty = Some(match merged_ty {
          Some(current) => store.intersection(vec![current, prop.ty]),
          None => prop.ty,
        });
        required |= prop.required;
        type_optional |= prop.type_optional;
        readonly |= prop.readonly;
        accessibility = merge_intersection_accessibility(accessibility, prop.accessibility);
        is_method |= prop.is_method;
      }
    }

    if let Some(ty) = merged_ty {
      props.push(PropertyEntry {
        key,
        ty,
        required,
        type_optional,
        readonly,
        accessibility,
        is_method,
      });
    }
  }

  props
}

fn find_property(shape: &ShapeInfo, key: &PropKey, store: &TypeStore) -> Option<PropertyEntry> {
  if let Some(prop) = shape.props.iter().find(|p| p.key == *key) {
    return Some(prop.clone());
  }
  for idx in shape.indexers.iter() {
    if indexer_matches(key, idx, store) {
      return Some(PropertyEntry {
        key: key.clone(),
        ty: idx.value_type,
        required: true,
        type_optional: false,
        readonly: idx.readonly,
        accessibility: None,
        is_method: false,
      });
    }
  }
  None
}

fn effective_type(prop: &PropertyEntry, store: &TypeStore) -> TypeId {
  if prop.type_optional && !prop.required {
    store.union(vec![prop.ty, store.primitive_ids().undefined])
  } else {
    prop.ty
  }
}

fn indexer_matches(key: &PropKey, idxer: &Indexer, store: &TypeStore) -> bool {
  indexer_accepts_key(key, idxer.key_type, store)
}

const MAX_INDEXER_KEY_MATCH_DEPTH: usize = 64;

fn indexer_accepts_key(key: &PropKey, idx_key: TypeId, store: &TypeStore) -> bool {
  indexer_accepts_key_inner(key, idx_key, store, 0)
}

fn indexer_accepts_key_inner(
  key: &PropKey,
  idx_key: TypeId,
  store: &TypeStore,
  depth: usize,
) -> bool {
  if depth >= MAX_INDEXER_KEY_MATCH_DEPTH {
    return false;
  }

  match store.type_kind(idx_key) {
    TypeKind::String | TypeKind::StringLiteral(_) => {
      matches!(key, PropKey::String(_) | PropKey::Number(_))
    }
    TypeKind::Number | TypeKind::NumberLiteral(_) => matches!(key, PropKey::Number(_)),
    TypeKind::Symbol | TypeKind::UniqueSymbol => matches!(key, PropKey::Symbol(_)),
    TypeKind::Union(members) => members
      .iter()
      .any(|member| indexer_accepts_key_inner(key, *member, store, depth + 1)),
    TypeKind::Intersection(members) => members
      .iter()
      .all(|member| indexer_accepts_key_inner(key, *member, store, depth + 1)),
    _ => false,
  }
}

fn merge_union_accessibility(
  current: Option<Accessibility>,
  next: Option<Accessibility>,
) -> Option<Accessibility> {
  match (current, next) {
    (None, other) => other,
    (Some(a), Some(b)) if a == b => Some(a),
    _ => None,
  }
}

fn merge_intersection_accessibility(
  current: Option<Accessibility>,
  next: Option<Accessibility>,
) -> Option<Accessibility> {
  match (current, next) {
    (None, other) => other,
    (Some(a), Some(b)) => Some(std::cmp::max(a, b)),
    (Some(a), None) => Some(a),
  }
}

fn intersect_signatures(
  shapes: &[ShapeInfo],
  store: &TypeStore,
  getter: impl Fn(&ShapeInfo) -> &Vec<SignatureId>,
) -> Vec<SignatureId> {
  if shapes.is_empty() {
    return Vec::new();
  }
  let mut base: Vec<SignatureId> = getter(&shapes[0]).clone();
  base.retain(|sig| shapes.iter().all(|shape| getter(shape).contains(sig)));
  sort_signatures(&mut base, store);
  base
}

fn union_signatures(
  shapes: &[ShapeInfo],
  store: &TypeStore,
  getter: impl Fn(&ShapeInfo) -> &Vec<SignatureId>,
) -> Vec<SignatureId> {
  let mut all: Vec<SignatureId> = shapes
    .iter()
    .flat_map(|shape| getter(shape).iter().copied())
    .collect();
  sort_signatures(&mut all, store);
  all
}

fn intersect_indexers(shapes: &[ShapeInfo], store: &TypeStore) -> Vec<Indexer> {
  if shapes.is_empty() {
    return Vec::new();
  }

  let mut keys: Vec<TypeId> = shapes[0]
    .indexers
    .iter()
    .map(|idx| store.canon(idx.key_type))
    .collect();
  keys.sort_by(|a, b| store.type_cmp(*a, *b));
  keys.dedup_by(|a, b| store.type_cmp(*a, *b) == std::cmp::Ordering::Equal);

  let mut result = Vec::new();
  for key in keys.into_iter() {
    let mut value: Option<TypeId> = None;
    let mut readonly = false;
    let mut present = true;
    for shape in shapes {
      let Some(idx) = shape
        .indexers
        .iter()
        .find(|idx| store.canon(idx.key_type) == key)
      else {
        present = false;
        break;
      };
      value = Some(match value {
        Some(current) => store.union(vec![current, idx.value_type]),
        None => idx.value_type,
      });
      readonly |= idx.readonly;
    }
    if present {
      result.push(Indexer {
        key_type: key,
        value_type: value.expect("indexer value set when present"),
        readonly,
      });
    }
  }

  result
}

fn union_indexers(shapes: &[ShapeInfo], store: &TypeStore) -> Vec<Indexer> {
  let mut merged: BTreeMap<TypeId, Indexer> = BTreeMap::new();
  for shape in shapes {
    for idx in shape.indexers.iter() {
      let key = store.canon(idx.key_type);
      merged
        .entry(key)
        .and_modify(|existing| {
          existing.value_type = store.intersection(vec![existing.value_type, idx.value_type]);
          existing.readonly |= idx.readonly;
        })
        .or_insert(Indexer {
          key_type: key,
          value_type: idx.value_type,
          readonly: idx.readonly,
        });
    }
  }
  merged.into_values().collect()
}

fn sort_properties(props: &mut Vec<PropertyEntry>, store: &TypeStore) {
  props.sort_by(|a, b| store.compare_prop_keys(&a.key, &b.key));
}

fn sort_signatures(signatures: &mut Vec<SignatureId>, store: &TypeStore) {
  signatures.sort_by(|a, b| store.compare_signatures(*a, *b));
  signatures.dedup();
}

fn sort_indexers(indexers: &mut Vec<impl IndexerKey>, store: &TypeStore) {
  indexers.sort_by(|a, b| {
    let a_key = store.canon(a.key());
    let b_key = store.canon(b.key());
    let ord = store.type_cmp(a_key, b_key);
    if ord != std::cmp::Ordering::Equal {
      return ord;
    }
    let a_value = store.canon(a.value());
    let b_value = store.canon(b.value());
    store.type_cmp(a_value, b_value)
  });
}

trait IndexerKey {
  fn key(&self) -> TypeId;
  fn value(&self) -> TypeId;
}

impl IndexerKey for Indexer {
  fn key(&self) -> TypeId {
    self.key_type
  }

  fn value(&self) -> TypeId {
    self.value_type
  }
}

impl IndexerKey for IndexerInfo {
  fn key(&self) -> TypeId {
    self.key_type
  }

  fn value(&self) -> TypeId {
    self.value_type
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn indexer_accepts_key_intersection_is_and() {
    let store = TypeStore::new();
    let primitives = store.primitive_ids();

    let union_key = store.union(vec![primitives.string, primitives.symbol]);
    let intersection_key = store.intersection(vec![union_key, primitives.string]);

    let sym_name = store.intern_name("sym");
    let key_symbol = PropKey::Symbol(sym_name);

    // Union is OR: (string | symbol) accepts symbol keys.
    assert!(indexer_accepts_key(&key_symbol, union_key, &store));

    // Intersection is AND: (string | symbol) & string behaves like `string`, so it rejects symbol keys.
    assert!(!indexer_accepts_key(&key_symbol, intersection_key, &store));
  }

  #[test]
  fn indexer_accepts_key_string_special_case_is_preserved_through_intersection() {
    let store = TypeStore::new();
    let primitives = store.primitive_ids();

    // (string | number) & string should behave like `string`: it accepts numeric property names.
    let intersection_key = store.intersection(vec![
      store.union(vec![primitives.string, primitives.number]),
      primitives.string,
    ]);
    assert!(indexer_accepts_key(
      &PropKey::Number(0),
      intersection_key,
      &store
    ));
  }
}
