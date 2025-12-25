use crate::ids::{DefId, ObjectId, TypeId, TypeParamId};
use crate::kind::{MappedModifier, MappedType, TemplateLiteralType, TypeKind};
use crate::shape::{PropData, PropKey, Property, Shape};
use crate::store::TypeStore;
use ahash::{AHashMap, AHashSet};
use ordered_float::OrderedFloat;
use std::cmp::Ordering;
use std::sync::Arc;

/// Expanded representation of a referenced type definition.
///
/// The `params` field lists formal type parameters that should be
/// substituted with the caller-provided type arguments when evaluating the
/// expanded `ty`.
#[derive(Clone, Debug)]
pub struct ExpandedType {
  pub params: Vec<TypeParamId>,
  pub ty: TypeId,
}

/// Provides lazy expansion of `TypeKind::Ref` nodes.
pub trait TypeExpander {
  /// Expand a referenced definition. Implementations may return `None` to
  /// indicate that the definition is unknown; in that case, the evaluator
  /// will leave the reference unexpanded.
  ///
  /// Implementations are expected to be pure; cycle detection and memoization
  /// are handled by [`TypeEvaluator`].
  fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct Substitution {
  bindings: Vec<(TypeParamId, TypeId)>,
}

impl Substitution {
  fn empty() -> Self {
    Self {
      bindings: Vec::new(),
    }
  }

  fn get(&self, param: TypeParamId) -> Option<TypeId> {
    self
      .bindings
      .binary_search_by_key(&param, |(p, _)| *p)
      .ok()
      .map(|idx| self.bindings[idx].1)
  }

  fn with(&self, param: TypeParamId, ty: TypeId) -> Self {
    let mut bindings = self.bindings.clone();
    match bindings.binary_search_by_key(&param, |(p, _)| *p) {
      Ok(idx) => bindings[idx] = (param, ty),
      Err(idx) => bindings.insert(idx, (param, ty)),
    };
    Self { bindings }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct EvalKey {
  ty: TypeId,
  subst: Substitution,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RefKey {
  def: DefId,
  args: Vec<TypeId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Key {
  Literal(PropKey),
  String,
  Number,
  Symbol,
}

impl Key {
  fn cmp(&self, other: &Self, store: &TypeStore) -> Ordering {
    let discr = self.discriminant().cmp(&other.discriminant());
    if discr != Ordering::Equal {
      return discr;
    }
    match (self, other) {
      (Key::Literal(a), Key::Literal(b)) => match (a, b) {
        (PropKey::String(a), PropKey::String(b)) | (PropKey::Symbol(a), PropKey::Symbol(b)) => {
          store.name(*a).cmp(&store.name(*b))
        }
        (PropKey::Number(a), PropKey::Number(b)) => a.cmp(b),
        _ => Ordering::Equal,
      },
      _ => Ordering::Equal,
    }
  }

  fn discriminant(&self) -> u8 {
    match self {
      Key::Literal(PropKey::String(_)) => 0,
      Key::Literal(PropKey::Number(_)) => 1,
      Key::Literal(PropKey::Symbol(_)) => 2,
      Key::String => 3,
      Key::Number => 4,
      Key::Symbol => 5,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum KeySet {
  Known(Vec<Key>),
  Unknown,
}

impl KeySet {
  fn known(mut keys: Vec<Key>, store: &TypeStore) -> Self {
    keys.sort_by(|a, b| a.cmp(b, store));
    keys.dedup();
    KeySet::Known(keys)
  }

  fn union(self, other: Self, store: &TypeStore) -> Self {
    match (self, other) {
      (KeySet::Known(mut a), KeySet::Known(mut b)) => {
        a.append(&mut b);
        KeySet::known(a, store)
      }
      _ => KeySet::Unknown,
    }
  }

  fn intersect(self, other: Self, store: &TypeStore) -> Self {
    match (self, other) {
      (KeySet::Known(a), KeySet::Known(b)) => {
        let mut out = Vec::new();
        for key in a {
          if b.iter().any(|k| k == &key) {
            out.push(key);
          }
        }
        KeySet::known(out, store)
      }
      _ => KeySet::Unknown,
    }
  }
}

#[derive(Clone, Debug)]
struct KeyInfo {
  key: Key,
  optional: bool,
  readonly: bool,
}

/// Evaluates and canonicalizes types with support for lazy reference expansion
/// and TypeScript-style operators (conditional/mapped/template/indexed/keyof).
pub struct TypeEvaluator<'a, E: TypeExpander> {
  store: Arc<TypeStore>,
  expander: &'a E,
  eval_cache: AHashMap<EvalKey, TypeId>,
  ref_cache: AHashMap<RefKey, TypeId>,
  eval_in_progress: AHashSet<EvalKey>,
  ref_in_progress: AHashSet<RefKey>,
  depth_limit: usize,
}

impl<'a, E: TypeExpander> std::fmt::Debug for TypeEvaluator<'a, E> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TypeEvaluator")
      .field("depth_limit", &self.depth_limit)
      .finish()
  }
}

impl<'a, E: TypeExpander> TypeEvaluator<'a, E> {
  const DEFAULT_DEPTH_LIMIT: usize = 64;

  pub fn new(store: Arc<TypeStore>, expander: &'a E) -> Self {
    Self {
      store,
      expander,
      eval_cache: AHashMap::new(),
      ref_cache: AHashMap::new(),
      eval_in_progress: AHashSet::new(),
      ref_in_progress: AHashSet::new(),
      depth_limit: Self::DEFAULT_DEPTH_LIMIT,
    }
  }

  pub fn with_depth_limit(mut self, limit: usize) -> Self {
    self.depth_limit = limit;
    self
  }

  pub fn evaluate(&mut self, ty: TypeId) -> TypeId {
    self.evaluate_with_subst(ty, &Substitution::empty(), 0)
  }

  fn evaluate_with_subst(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    if depth >= self.depth_limit {
      return ty;
    }
    let key = EvalKey {
      ty,
      subst: subst.clone(),
    };
    if let Some(cached) = self.eval_cache.get(&key) {
      return *cached;
    }
    if self.eval_in_progress.contains(&key) {
      return ty;
    }
    self.eval_in_progress.insert(key.clone());
    let result = match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => match subst.get(id) {
        Some(mapped) => self.evaluate_with_subst(mapped, subst, depth + 1),
        None => ty,
      },
      TypeKind::Union(members) => {
        let evaluated: Vec<_> = members
          .into_iter()
          .map(|m| self.evaluate_with_subst(m, subst, depth + 1))
          .collect();
        self.store.union(evaluated)
      }
      TypeKind::Intersection(members) => {
        let evaluated: Vec<_> = members
          .into_iter()
          .map(|m| self.evaluate_with_subst(m, subst, depth + 1))
          .collect();
        self.store.intersection(evaluated)
      }
      TypeKind::Array { ty, readonly } => {
        let elem = self.evaluate_with_subst(ty, subst, depth + 1);
        self
          .store
          .intern_type(TypeKind::Array { ty: elem, readonly })
      }
      TypeKind::Tuple(elems) => {
        let evaluated = elems
          .into_iter()
          .map(|elem| crate::TupleElem {
            ty: self.evaluate_with_subst(elem.ty, subst, depth + 1),
            optional: elem.optional,
            rest: elem.rest,
            readonly: elem.readonly,
          })
          .collect();
        self.store.intern_type(TypeKind::Tuple(evaluated))
      }
      TypeKind::Object(obj) => self.evaluate_object(obj, subst, depth + 1),
      TypeKind::Callable { overloads } => {
        // Signatures may reference type parameters; eagerly substitute.
        let overloads: Vec<_> = overloads
          .into_iter()
          .map(|sig| self.evaluate_signature(sig, subst, depth + 1))
          .collect();
        self.store.intern_type(TypeKind::Callable { overloads })
      }
      TypeKind::Ref { def, args } => self.evaluate_ref(def, args, subst, depth + 1),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => self.evaluate_conditional(
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
        subst,
        depth + 1,
      ),
      TypeKind::Mapped(mapped) => self.evaluate_mapped(mapped, subst, depth + 1),
      TypeKind::TemplateLiteral(tpl) => self.evaluate_template_literal(tpl, subst, depth + 1),
      TypeKind::IndexedAccess { obj, index } => {
        self.evaluate_indexed_access(obj, index, subst, depth + 1)
      }
      TypeKind::KeyOf(inner) => self.evaluate_keyof(inner, subst, depth + 1),
      other => self.store.intern_type(other),
    };
    self.eval_in_progress.remove(&key);
    self.eval_cache.insert(key, result);
    result
  }

  fn evaluate_signature(
    &mut self,
    sig: crate::SignatureId,
    subst: &Substitution,
    depth: usize,
  ) -> crate::SignatureId {
    let mut sig = self.store.signature(sig);
    sig.params.iter_mut().for_each(|param| {
      param.ty = self.evaluate_with_subst(param.ty, subst, depth + 1);
    });
    sig.ret = self.evaluate_with_subst(sig.ret, subst, depth + 1);
    if let Some(this) = sig.this_param.as_mut() {
      *this = self.evaluate_with_subst(*this, subst, depth + 1);
    }
    self.store.intern_signature(sig)
  }

  fn evaluate_object(&mut self, obj: ObjectId, subst: &Substitution, depth: usize) -> TypeId {
    let object = self.store.object(obj);
    let mut shape = self.store.shape(object.shape);
    for prop in shape.properties.iter_mut() {
      prop.data.ty = self.evaluate_with_subst(prop.data.ty, subst, depth + 1);
    }
    for idx in shape.indexers.iter_mut() {
      idx.key_type = self.evaluate_with_subst(idx.key_type, subst, depth + 1);
      idx.value_type = self.evaluate_with_subst(idx.value_type, subst, depth + 1);
    }
    shape.call_signatures = shape
      .call_signatures
      .into_iter()
      .map(|sig| self.evaluate_signature(sig, subst, depth + 1))
      .collect();
    shape.construct_signatures = shape
      .construct_signatures
      .into_iter()
      .map(|sig| self.evaluate_signature(sig, subst, depth + 1))
      .collect();
    let shape_id = self.store.intern_shape(shape);
    let obj_id = self
      .store
      .intern_object(crate::ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj_id))
  }

  fn evaluate_ref(
    &mut self,
    def: DefId,
    args: Vec<TypeId>,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    let evaluated_args: Vec<_> = args
      .into_iter()
      .map(|arg| self.evaluate_with_subst(arg, subst, depth + 1))
      .collect();
    let key = RefKey {
      def,
      args: evaluated_args.clone(),
    };
    if let Some(cached) = self.ref_cache.get(&key) {
      return *cached;
    }
    if self.ref_in_progress.contains(&key) {
      return self.store.intern_type(TypeKind::Ref {
        def,
        args: evaluated_args,
      });
    }
    self.ref_in_progress.insert(key.clone());
    let expanded = self
      .expander
      .expand(&self.store, def, &evaluated_args)
      .map(|expanded| {
        let mut next_subst = subst.clone();
        for (idx, param) in expanded.params.iter().enumerate() {
          if let Some(arg) = evaluated_args.get(idx) {
            next_subst = next_subst.with(*param, *arg);
          }
        }
        self.evaluate_with_subst(expanded.ty, &next_subst, depth + 1)
      })
      .unwrap_or_else(|| {
        self.store.intern_type(TypeKind::Ref {
          def,
          args: evaluated_args,
        })
      });
    self.ref_in_progress.remove(&key);
    self.ref_cache.insert(key, expanded);
    expanded
  }

  fn evaluate_conditional(
    &mut self,
    check: TypeId,
    extends: TypeId,
    true_ty: TypeId,
    false_ty: TypeId,
    distributive: bool,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    let raw_check = self.store.type_kind(check);
    let check_eval = self.evaluate_with_subst(check, subst, depth + 1);
    let extends_eval = self.evaluate_with_subst(extends, subst, depth + 1);
    if distributive {
      if let TypeKind::Union(members) = self.store.type_kind(check_eval) {
        let mut results = Vec::new();
        for member in members {
          let mut inner_subst = subst.clone();
          if let TypeKind::TypeParam(param) = raw_check {
            inner_subst = inner_subst.with(param, member);
          }
          results.push(self.evaluate_conditional(
            member,
            extends_eval,
            true_ty,
            false_ty,
            false,
            &inner_subst,
            depth + 1,
          ));
        }
        return self.store.union(results);
      }
    }

    let branch = if self.is_assignable(check_eval, extends_eval, subst, depth + 1) {
      true_ty
    } else {
      false_ty
    };
    self.evaluate_with_subst(branch, subst, depth + 1)
  }

  fn evaluate_mapped(&mut self, mapped: MappedType, subst: &Substitution, depth: usize) -> TypeId {
    let entries = self.mapped_entries(mapped.source, subst, depth + 1);

    let mut properties = Vec::new();
    for entry in entries {
      let key_tys = self.mapped_key_type_ids(&entry.key);
      let mut inner_subst = subst.clone();
      inner_subst = inner_subst.with(mapped.param, key_tys.original);
      let value_ty = self.evaluate_with_subst(mapped.value, &inner_subst, depth + 1);
      let readonly = match mapped.readonly {
        MappedModifier::Preserve => entry.readonly,
        MappedModifier::Add => true,
        MappedModifier::Remove => false,
      };
      let optional = match mapped.optional {
        MappedModifier::Preserve => entry.optional,
        MappedModifier::Add => true,
        MappedModifier::Remove => false,
      };

      let mut remapped_keys = self.remap_mapped_key(&mapped, &entry.key, &inner_subst, depth + 1);
      if remapped_keys.is_empty() {
        if let Key::Literal(prop_key) = entry.key {
          remapped_keys.push(prop_key);
        }
      }

      for prop_key in remapped_keys {
        properties.push(Property {
          key: prop_key,
          data: PropData {
            ty: value_ty,
            optional,
            readonly,
            accessibility: None,
            is_method: false,
            declared_on: None,
          },
        });
      }
    }

    let shape = Shape {
      properties,
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      indexers: Vec::new(),
    };
    let shape_id = self.store.intern_shape(shape);
    let obj = self
      .store
      .intern_object(crate::ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn remap_mapped_key(
    &mut self,
    mapped: &MappedType,
    entry: &Key,
    subst: &Substitution,
    depth: usize,
  ) -> Vec<PropKey> {
    let remap_ty = mapped.as_type.or(mapped.name_type);
    let Some(remap_ty) = remap_ty else {
      return Vec::new();
    };
    let key_tys = self.mapped_key_type_ids(entry);
    let mut inner_subst = subst.clone();
    inner_subst = inner_subst.with(mapped.param, key_tys.original);
    let evaluated = self.evaluate_with_subst(remap_ty, &inner_subst, depth + 1);
    self.keys_to_prop_keys(evaluated)
  }

  fn keys_to_prop_keys(&mut self, ty: TypeId) -> Vec<PropKey> {
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => members
        .into_iter()
        .flat_map(|member| self.keys_to_prop_keys(member))
        .collect(),
      TypeKind::StringLiteral(id) => vec![PropKey::String(id)],
      TypeKind::NumberLiteral(num) => vec![PropKey::Number(num.0 as i64)],
      TypeKind::TemplateLiteral(tpl) => self
        .compute_template_strings(&tpl, &Substitution::empty(), 0)
        .unwrap_or_default()
        .into_iter()
        .map(|s| PropKey::String(self.store.intern_name(s)))
        .collect(),
      _ => Vec::new(),
    }
  }

  fn mapped_key_type_ids(&self, key: &Key) -> MappedKeyTypes {
    let primitives = self.store.primitive_ids();
    match key {
      Key::Literal(PropKey::String(id)) => MappedKeyTypes {
        original: self.store.intern_type(TypeKind::StringLiteral(*id)),
      },
      Key::Literal(PropKey::Number(num)) => MappedKeyTypes {
        original: self
          .store
          .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(*num as f64))),
      },
      Key::Literal(PropKey::Symbol(_)) => MappedKeyTypes {
        original: primitives.symbol,
      },
      Key::String => MappedKeyTypes {
        original: primitives.string,
      },
      Key::Number => MappedKeyTypes {
        original: primitives.number,
      },
      Key::Symbol => MappedKeyTypes {
        original: primitives.symbol,
      },
    }
  }

  fn mapped_entries(&mut self, source: TypeId, subst: &Substitution, depth: usize) -> Vec<KeyInfo> {
    if let TypeKind::KeyOf(inner) = self.store.type_kind(source) {
      let evaluated_inner = self.evaluate_with_subst(inner, subst, depth + 1);
      return self.keys_from_type_as_entries(evaluated_inner, subst, depth + 1);
    }

    let evaluated_source = self.evaluate_with_subst(source, subst, depth + 1);
    match self.store.type_kind(evaluated_source) {
      TypeKind::Union(members) => {
        let mut entries = Vec::new();
        for member in members {
          entries.extend(self.keys_from_type_as_entries(member, subst, depth + 1));
        }
        self.dedup_entries(entries)
      }
      TypeKind::Intersection(members) => {
        let mut entries = Vec::new();
        for member in members {
          entries.extend(self.keys_from_type_as_entries(member, subst, depth + 1));
        }
        self.dedup_entries(entries)
      }
      other => self.keys_from_type_as_entries(self.store.intern_type(other), subst, depth + 1),
    }
  }

  fn dedup_entries(&self, entries: Vec<KeyInfo>) -> Vec<KeyInfo> {
    let mut merged: AHashMap<Key, (bool, bool)> = AHashMap::new();
    for entry in entries.into_iter() {
      merged
        .entry(entry.key)
        .and_modify(|existing| {
          existing.0 |= entry.optional;
          existing.1 |= entry.readonly;
        })
        .or_insert((entry.optional, entry.readonly));
    }
    let mut out: Vec<KeyInfo> = merged
      .into_iter()
      .map(|(key, (optional, readonly))| KeyInfo {
        key,
        optional,
        readonly,
      })
      .collect();
    out.sort_by(|a, b| a.key.cmp(&b.key, &self.store));
    out
  }

  fn evaluate_template_literal(
    &mut self,
    tpl: TemplateLiteralType,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    let strings = self.compute_template_strings(&tpl, subst, depth + 1);
    match strings {
      Some(strings) => {
        if strings.is_empty() {
          return self.store.primitive_ids().never;
        }
        let mut types = Vec::new();
        for s in strings {
          let name = self.store.intern_name(s);
          types.push(self.store.intern_type(TypeKind::StringLiteral(name)));
        }
        self.store.union(types)
      }
      None => self.store.primitive_ids().string,
    }
  }

  fn evaluate_indexed_access(
    &mut self,
    obj: TypeId,
    index: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> TypeId {
    let obj_eval = self.evaluate_with_subst(obj, subst, depth + 1);
    let index_eval = self.evaluate_with_subst(index, subst, depth + 1);

    if let TypeKind::Union(keys) = self.store.type_kind(index_eval) {
      let mut results = Vec::new();
      for key in keys {
        results.push(self.evaluate_indexed_access(obj_eval, key, subst, depth + 1));
      }
      return self.store.union(results);
    }

    if let TypeKind::Union(objs) = self.store.type_kind(obj_eval) {
      let mut results = Vec::new();
      for member in objs {
        results.push(self.evaluate_indexed_access(member, index_eval, subst, depth + 1));
      }
      return self.store.union(results);
    }

    match self.store.type_kind(obj_eval) {
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        match self.keys_from_index_type(index_eval) {
          KeySet::Known(keys) => {
            let mut hits = Vec::new();
            for key in keys {
              self.collect_property_type(&shape, &key, &mut hits);
            }
            if hits.is_empty() {
              self.store.primitive_ids().never
            } else {
              self.store.union(hits)
            }
          }
          KeySet::Unknown => self.store.primitive_ids().unknown,
        }
      }
      TypeKind::Array { ty, .. } => match self.store.type_kind(index_eval) {
        TypeKind::NumberLiteral(_) | TypeKind::Number => {
          self.evaluate_with_subst(ty, subst, depth + 1)
        }
        _ => self.store.primitive_ids().unknown,
      },
      TypeKind::Tuple(elems) => match self.store.type_kind(index_eval) {
        TypeKind::NumberLiteral(num) => {
          let idx = num.0 as usize;
          if let Some(elem) = elems.get(idx) {
            let mut ty = self.evaluate_with_subst(elem.ty, subst, depth + 1);
            if elem.optional {
              ty = self
                .store
                .union(vec![ty, self.store.primitive_ids().undefined]);
            }
            ty
          } else {
            self.store.primitive_ids().undefined
          }
        }
        _ => {
          let mut members = Vec::new();
          for elem in elems {
            let mut ty = self.evaluate_with_subst(elem.ty, subst, depth + 1);
            if elem.optional {
              ty = self
                .store
                .union(vec![ty, self.store.primitive_ids().undefined]);
            }
            members.push(ty);
          }
          self.store.union(members)
        }
      },
      _ => self.store.primitive_ids().unknown,
    }
  }

  fn evaluate_keyof(&mut self, inner: TypeId, subst: &Substitution, depth: usize) -> TypeId {
    let keyset = self.keys_from_type(inner, subst, depth + 1);
    match keyset {
      KeySet::Known(keys) => {
        let mut members = Vec::new();
        for key in keys {
          match key {
            Key::Literal(PropKey::String(id)) => {
              members.push(self.store.intern_type(TypeKind::StringLiteral(id)));
            }
            Key::Literal(PropKey::Number(num)) => {
              members.push(
                self
                  .store
                  .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(num as f64))),
              );
            }
            Key::Literal(PropKey::Symbol(_)) => members.push(self.store.primitive_ids().symbol),
            Key::String => members.push(self.store.primitive_ids().string),
            Key::Number => members.push(self.store.primitive_ids().number),
            Key::Symbol => members.push(self.store.primitive_ids().symbol),
          }
        }
        self.store.union(members)
      }
      KeySet::Unknown => self.store.union(vec![
        self.store.primitive_ids().string,
        self.store.primitive_ids().number,
        self.store.primitive_ids().symbol,
      ]),
    }
  }

  fn keys_from_index_type(&mut self, ty: TypeId) -> KeySet {
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut keys = Vec::new();
        for member in members {
          match self.keys_from_index_type(member) {
            KeySet::Known(mut inner) => keys.append(&mut inner),
            KeySet::Unknown => return KeySet::Unknown,
          }
        }
        KeySet::known(keys, &self.store)
      }
      TypeKind::StringLiteral(id) => {
        KeySet::known(vec![Key::Literal(PropKey::String(id))], &self.store)
      }
      TypeKind::NumberLiteral(num) => KeySet::known(
        vec![Key::Literal(PropKey::Number(num.0 as i64))],
        &self.store,
      ),
      TypeKind::TemplateLiteral(tpl) => {
        match self.compute_template_strings(&tpl, &Substitution::empty(), 0) {
          Some(strings) => KeySet::known(
            strings
              .into_iter()
              .map(|s| Key::Literal(PropKey::String(self.store.intern_name(s))))
              .collect(),
            &self.store,
          ),
          None => KeySet::Unknown,
        }
      }
      TypeKind::String => KeySet::known(vec![Key::String], &self.store),
      TypeKind::Number => KeySet::known(vec![Key::Number], &self.store),
      _ => KeySet::Unknown,
    }
  }

  fn keys_from_type(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> KeySet {
    let evaluated = self.evaluate_with_subst(ty, subst, depth + 1);
    self.keys_from_type_id(evaluated, subst, depth + 1)
  }

  fn keys_from_type_as_entries(
    &mut self,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> Vec<KeyInfo> {
    match self.store.type_kind(ty) {
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        let mut merged: AHashMap<Key, (bool, bool)> = AHashMap::new();
        for prop in shape.properties.iter() {
          merged
            .entry(Key::Literal(prop.key.clone()))
            .and_modify(|entry| {
              entry.0 |= prop.data.optional;
              entry.1 |= prop.data.readonly;
            })
            .or_insert((prop.data.optional, prop.data.readonly));
        }
        for idxer in shape.indexers.iter() {
          let key = match self.store.type_kind(idxer.key_type) {
            TypeKind::String => Key::String,
            TypeKind::Number => Key::Number,
            _ => continue,
          };
          merged
            .entry(key)
            .and_modify(|entry| entry.1 |= idxer.readonly)
            .or_insert((false, idxer.readonly));
        }
        let mut entries: Vec<KeyInfo> = merged
          .into_iter()
          .map(|(key, (optional, readonly))| KeyInfo {
            key,
            optional,
            readonly,
          })
          .collect();
        entries.sort_by(|a, b| a.key.cmp(&b.key, &self.store));
        entries
      }
      _ => match self.keys_from_type_id(ty, subst, depth) {
        KeySet::Known(keys) => keys
          .into_iter()
          .map(|key| KeyInfo {
            key,
            optional: false,
            readonly: false,
          })
          .collect(),
        KeySet::Unknown => Vec::new(),
      },
    }
  }

  fn keys_from_type_id(&mut self, ty: TypeId, subst: &Substitution, depth: usize) -> KeySet {
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut iter = members.into_iter();
        let Some(first) = iter.next() else {
          return KeySet::known(Vec::new(), &self.store);
        };
        let mut acc = self.keys_from_type(first, subst, depth + 1);
        for member in iter {
          acc = acc.intersect(self.keys_from_type(member, subst, depth + 1), &self.store);
        }
        acc
      }
      TypeKind::Intersection(members) => {
        let mut acc = KeySet::known(Vec::new(), &self.store);
        for member in members {
          let keys = self.keys_from_type(member, subst, depth + 1);
          acc = acc.union(keys, &self.store);
        }
        acc
      }
      TypeKind::Object(obj) => {
        let mut keys = Vec::new();
        let shape = self.store.shape(self.store.object(obj).shape);
        for prop in shape.properties.iter() {
          keys.push(Key::Literal(prop.key.clone()));
        }
        for idx in shape.indexers.iter() {
          match self.store.type_kind(idx.key_type) {
            TypeKind::String => keys.push(Key::String),
            TypeKind::Number => keys.push(Key::Number),
            _ => {}
          }
        }
        KeySet::known(keys, &self.store)
      }
      TypeKind::Tuple(elems) => {
        let mut keys = Vec::new();
        for (idx, elem) in elems.iter().enumerate() {
          keys.push(Key::Literal(PropKey::Number(idx as i64)));
          if elem.rest {
            keys.push(Key::Number);
            break;
          }
        }
        KeySet::known(keys, &self.store)
      }
      TypeKind::Array { .. } => KeySet::known(vec![Key::Number], &self.store),
      TypeKind::TemplateLiteral(tpl) => {
        match self.compute_template_strings(&tpl, subst, depth + 1) {
          Some(strings) => KeySet::known(
            strings
              .into_iter()
              .map(|s| Key::Literal(PropKey::String(self.store.intern_name(s))))
              .collect(),
            &self.store,
          ),
          None => KeySet::Unknown,
        }
      }
      TypeKind::StringLiteral(id) => {
        KeySet::known(vec![Key::Literal(PropKey::String(id))], &self.store)
      }
      TypeKind::NumberLiteral(num) => KeySet::known(
        vec![Key::Literal(PropKey::Number(num.0 as i64))],
        &self.store,
      ),
      TypeKind::UniqueSymbol => KeySet::known(vec![Key::Symbol], &self.store),
      TypeKind::Symbol => KeySet::known(vec![Key::Symbol], &self.store),
      TypeKind::String => KeySet::known(vec![Key::String], &self.store),
      TypeKind::Number => KeySet::known(vec![Key::Number], &self.store),
      _ => KeySet::Unknown,
    }
  }

  fn collect_property_type(&self, shape: &Shape, key: &Key, hits: &mut Vec<TypeId>) {
    for prop in shape.properties.iter() {
      if match (key, &prop.key) {
        (Key::Literal(a), b) => a == b,
        (Key::String, PropKey::String(_)) => true,
        (Key::Number, PropKey::Number(_)) => true,
        (Key::Symbol, PropKey::Symbol(_)) => true,
        _ => false,
      } {
        let mut ty = prop.data.ty;
        if prop.data.optional {
          ty = self
            .store
            .union(vec![ty, self.store.primitive_ids().undefined]);
        }
        hits.push(ty);
      }
    }
    for idxer in shape.indexers.iter() {
      let matches = match (key, self.store.type_kind(idxer.key_type)) {
        (Key::String, TypeKind::String) => true,
        (Key::Number, TypeKind::Number) => true,
        (Key::Literal(PropKey::String(_)), TypeKind::String) => true,
        (Key::Literal(PropKey::Number(_)), TypeKind::Number) => true,
        _ => false,
      };
      if matches {
        hits.push(idxer.value_type);
      }
    }
  }

  fn compute_template_strings(
    &mut self,
    tpl: &TemplateLiteralType,
    subst: &Substitution,
    depth: usize,
  ) -> Option<Vec<String>> {
    let mut acc = vec![tpl.head.clone()];
    for span in tpl.spans.iter() {
      let atom_strings = self.template_atom_strings(span.ty, subst, depth + 1)?;
      let mut next = Vec::new();
      for base in &acc {
        for atom in &atom_strings {
          let mut new = base.clone();
          new.push_str(atom);
          new.push_str(&span.literal);
          next.push(new);
        }
      }
      acc = next;
    }
    acc.sort();
    acc.dedup();
    Some(acc)
  }

  fn template_atom_strings(
    &mut self,
    ty: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> Option<Vec<String>> {
    let evaluated = self.evaluate_with_subst(ty, subst, depth + 1);
    match self.store.type_kind(evaluated) {
      TypeKind::StringLiteral(id) => Some(vec![self.store.name(id)]),
      TypeKind::NumberLiteral(num) => Some(vec![num.0.to_string()]),
      TypeKind::BooleanLiteral(val) => Some(vec![val.to_string()]),
      TypeKind::TemplateLiteral(tpl) => self.compute_template_strings(&tpl, subst, depth + 1),
      TypeKind::Union(members) => {
        let mut out = Vec::new();
        for member in members {
          let Some(mut vals) = self.template_atom_strings(member, subst, depth + 1) else {
            return None;
          };
          out.append(&mut vals);
        }
        Some(out)
      }
      TypeKind::Never => Some(Vec::new()),
      _ => None,
    }
  }

  fn is_assignable(
    &mut self,
    src: TypeId,
    target: TypeId,
    subst: &Substitution,
    depth: usize,
  ) -> bool {
    if src == target {
      return true;
    }
    match (self.store.type_kind(src), self.store.type_kind(target)) {
      (_, TypeKind::Any) => true,
      (TypeKind::Any, _) => true,
      (_, TypeKind::Unknown) => true,
      (TypeKind::Never, _) => true,
      (TypeKind::Union(members), target_kind) => members.into_iter().all(|m| {
        self.is_assignable(
          m,
          self.store.intern_type(target_kind.clone()),
          subst,
          depth + 1,
        )
      }),
      (src_kind, TypeKind::Union(members)) => members.into_iter().any(|member| {
        self.is_assignable(
          self.store.intern_type(src_kind.clone()),
          member,
          subst,
          depth + 1,
        )
      }),
      (TypeKind::BooleanLiteral(_), TypeKind::Boolean) => true,
      (TypeKind::NumberLiteral(_), TypeKind::Number) => true,
      (TypeKind::StringLiteral(_), TypeKind::String) => true,
      (TypeKind::BigIntLiteral(_), TypeKind::BigInt) => true,
      (TypeKind::TemplateLiteral(_), TypeKind::String) => true,
      (TypeKind::TypeParam(param), other) => match subst.get(param) {
        Some(mapped) => self.is_assignable(mapped, self.store.intern_type(other), subst, depth + 1),
        None => false,
      },
      _ => false,
    }
  }
}

struct MappedKeyTypes {
  original: TypeId,
}
