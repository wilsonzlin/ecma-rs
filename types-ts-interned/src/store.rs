use crate::display::TypeDisplay;
use crate::ids::NameId;
use crate::ids::ObjectId;
use crate::ids::ShapeId;
use crate::ids::SignatureId;
use crate::ids::TypeId;
use crate::ids::TypeParamId;
use crate::kind::CompositeKind;
use crate::kind::TypeKind;
use crate::options::TypeOptions;
use crate::shape::Indexer;
use crate::shape::ObjectInterner;
use crate::shape::ObjectType;
use crate::shape::Property;
use crate::shape::Shape;
use crate::shape::ShapeInterner;
use crate::signature::Param;
use crate::signature::Signature;
use crate::signature::SignatureInterner;
use ahash::RandomState;
use parking_lot::RwLock;
use std::cmp::Ordering;
use std::hash::BuildHasher;
use std::hash::Hasher;
use std::sync::Arc;

#[derive(Default, Debug)]
struct TypeInterner {
  items: Vec<TypeKind>,
  map: ahash::AHashMap<TypeKind, TypeId>,
}

impl TypeInterner {
  fn intern(&mut self, kind: TypeKind) -> TypeId {
    if let Some(id) = self.map.get(&kind) {
      return *id;
    }
    let id = TypeId(self.items.len() as u32);
    self.items.push(kind.clone());
    self.map.insert(kind, id);
    id
  }
}

#[derive(Default, Debug)]
struct NameInterner {
  by_name: ahash::AHashMap<String, NameId>,
  by_id: ahash::AHashMap<NameId, String>,
}

impl NameInterner {
  fn hash_with_seeds(name: &str, seeds: (u64, u64, u64, u64), salt: u64) -> u64 {
    let mut hasher = RandomState::with_seeds(seeds.0, seeds.1, seeds.2, seeds.3).build_hasher();
    hasher.write_u64(salt);
    hasher.write(name.as_bytes());
    hasher.finish()
  }

  fn hash_name(name: &str, salt: u64) -> NameId {
    const NAME_HASH_KEY1: u64 = 0x9e37_79b9_7f4a_7c15;
    const NAME_HASH_KEY2: u64 = 0xc2b2_ae3d_27d4_eb4f;
    const NAME_HASH_KEY3: u64 = 0x1656_67b1_9e37_79f9;
    const NAME_HASH_KEY4: u64 = 0x85eb_ca6b_c8f6_9b07;

    let primary = Self::hash_with_seeds(
      name,
      (
        NAME_HASH_KEY1,
        NAME_HASH_KEY2,
        NAME_HASH_KEY3,
        NAME_HASH_KEY4,
      ),
      salt,
    );
    let secondary = Self::hash_with_seeds(
      name,
      (
        NAME_HASH_KEY4 ^ 0xa076_1d64_78bd_642f,
        NAME_HASH_KEY3 ^ 0xe703_7ed1_a0b4_28db,
        NAME_HASH_KEY2 ^ 0x8ebc_6af0_6737_7ee8,
        NAME_HASH_KEY1 ^ 0x5888_5cdd_54d4_641f,
      ),
      salt,
    );
    NameId(primary.rotate_left(5) ^ secondary)
  }

  fn intern(&mut self, name: impl Into<String>) -> NameId {
    let name = name.into();
    if let Some(id) = self.by_name.get(&name) {
      return *id;
    }

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

  fn name(&self, id: NameId) -> &str {
    self
      .by_id
      .get(&id)
      .map(|s| s.as_str())
      .expect("NameId not interned")
  }
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug)]
pub struct TypeStore {
  types: RwLock<TypeInterner>,
  shapes: RwLock<ShapeInterner>,
  objects: RwLock<ObjectInterner>,
  names: RwLock<NameInterner>,
  signatures: RwLock<SignatureInterner>,
  options: TypeOptions,
  primitives: PrimitiveIds,
}

impl TypeStore {
  pub fn new() -> Arc<Self> {
    Self::with_options(TypeOptions::default())
  }

  pub fn with_options(options: TypeOptions) -> Arc<Self> {
    let mut types = TypeInterner::default();
    let primitives = PrimitiveIds {
      any: types.intern(TypeKind::Any),
      unknown: types.intern(TypeKind::Unknown),
      never: types.intern(TypeKind::Never),
      void: types.intern(TypeKind::Void),
      null: types.intern(TypeKind::Null),
      undefined: types.intern(TypeKind::Undefined),
      boolean: types.intern(TypeKind::Boolean),
      number: types.intern(TypeKind::Number),
      string: types.intern(TypeKind::String),
      bigint: types.intern(TypeKind::BigInt),
      symbol: types.intern(TypeKind::Symbol),
      unique_symbol: types.intern(TypeKind::UniqueSymbol),
    };

    Arc::new(Self {
      types: RwLock::new(types),
      shapes: Default::default(),
      objects: Default::default(),
      names: Default::default(),
      signatures: Default::default(),
      options,
      primitives,
    })
  }

  pub fn options(&self) -> TypeOptions {
    self.options
  }

  pub fn primitive_ids(&self) -> PrimitiveIds {
    self.primitives
  }

  pub fn name(&self, id: NameId) -> String {
    let guard = self.names.read();
    guard.name(id).to_owned()
  }

  pub fn intern_name(&self, name: impl Into<String>) -> NameId {
    self.names.write().intern(name)
  }

  pub fn signature(&self, id: SignatureId) -> Signature {
    let guard = self.signatures.read();
    guard.items[id.index()].clone()
  }

  pub fn intern_signature(&self, signature: Signature) -> SignatureId {
    let mut signature = signature;
    for param in signature.params.iter_mut() {
      param.ty = self.canon(param.ty);
    }
    signature.ret = self.canon(signature.ret);
    if let Some(this) = signature.this_param.as_mut() {
      *this = self.canon(*this);
    }
    let mut guard = self.signatures.write();
    guard.intern(signature)
  }

  pub fn shape(&self, id: ShapeId) -> Shape {
    let guard = self.shapes.read();
    guard.items[id.index()].clone()
  }

  pub fn object(&self, id: ObjectId) -> ObjectType {
    let guard = self.objects.read();
    guard.items[id.index()].clone()
  }

  pub fn type_kind(&self, id: TypeId) -> TypeKind {
    let guard = self.types.read();
    guard.items[id.index()].clone()
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
        .sort_by(|a, b| a.key.cmp_with(&b.key, &|id| names.name(id).to_owned()));
    }
    // Merge duplicate property keys deterministically by intersecting their
    // types, requiring presence if any declaration is required, propagating
    // readonly if any declaration is readonly, and keeping the most
    // restrictive accessibility modifier if present.
    let mut merged_properties: Vec<Property> = Vec::with_capacity(shape.properties.len());
    for prop in shape.properties.into_iter() {
      if let Some(last) = merged_properties.last_mut() {
        if last.key == prop.key {
          last.data.ty = self.intersection(vec![last.data.ty, prop.data.ty]);
          last.data.optional = last.data.optional && prop.data.optional;
          last.data.readonly = last.data.readonly || prop.data.readonly;
          last.data.is_method = last.data.is_method || prop.data.is_method;
          if last.data.declared_on.is_none() {
            last.data.declared_on = prop.data.declared_on;
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
    }
    shape.properties = merged_properties;
    shape
      .call_signatures
      .sort_by(|a, b| self.signature_cmp(*a, *b));
    shape.call_signatures.dedup();
    shape
      .construct_signatures
      .sort_by(|a, b| self.signature_cmp(*a, *b));
    shape.construct_signatures.dedup();
    shape
      .indexers
      .sort_by(|a, b| match self.type_cmp(a.key_type, b.key_type) {
        Ordering::Equal => self.type_cmp(a.value_type, b.value_type),
        other => other,
      });

    let mut guard = self.shapes.write();
    guard.intern(shape)
  }

  pub fn intern_object(&self, object: ObjectType) -> ObjectId {
    let mut guard = self.objects.write();
    guard.intern(object)
  }

  pub fn intern_type(&self, kind: TypeKind) -> TypeId {
    let kind = self.canonicalize_kind(kind);
    match kind {
      TypeKind::Union(members) => self.union(members),
      TypeKind::Intersection(members) => self.intersection(members),
      other => {
        let mut guard = self.types.write();
        guard.intern(other)
      }
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
      TypeKind::Mapped(mut mapped) => {
        mapped.source = self.canon(mapped.source);
        mapped.value = self.canon(mapped.value);
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
      TypeKind::IndexedAccess { obj, index } => TypeKind::IndexedAccess {
        obj: self.canon(obj),
        index: self.canon(index),
      },
      TypeKind::KeyOf(inner) => TypeKind::KeyOf(self.canon(inner)),
      TypeKind::Callable { mut overloads } => {
        overloads.sort_by(|a, b| self.signature_cmp(*a, *b));
        overloads.dedup();
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

    let mut guard = self.types.write();
    guard.intern(TypeKind::Union(flat))
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
    for member in &flat {
      match self.type_kind(*member) {
        TypeKind::BooleanLiteral(_) => has_boolean_literal = true,
        TypeKind::NumberLiteral(_) => has_number_literal = true,
        TypeKind::StringLiteral(_) => has_string_literal = true,
        TypeKind::BigIntLiteral(_) => has_bigint_literal = true,
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

    // unknown acts as identity; if no other members, it is the result.
    if flat.is_empty() {
      return self.primitives.unknown;
    }

    self.sort_and_dedup(&mut flat);
    if flat.len() == 1 {
      return flat[0];
    }

    let mut guard = self.types.write();
    guard.intern(TypeKind::Intersection(flat))
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
    match (a_kind, b_kind) {
      (TypeKind::BooleanLiteral(a), TypeKind::BooleanLiteral(b)) => a.cmp(&b),
      (TypeKind::NumberLiteral(a), TypeKind::NumberLiteral(b)) => a.cmp(&b),
      (TypeKind::StringLiteral(a), TypeKind::StringLiteral(b)) => self.name(a).cmp(&self.name(b)),
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
        let mut idx = 0;
        loop {
          let Some(left) = a.get(idx) else {
            return a.len().cmp(&b.len());
          };
          let Some(right) = b.get(idx) else {
            return a.len().cmp(&b.len());
          };
          let ord = self.signature_cmp(*left, *right);
          if ord != Ordering::Equal {
            return ord;
          }
          idx += 1;
        }
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
      (TypeKind::Infer(a), TypeKind::Infer(b)) => a.0.cmp(&b.0),
      (TypeKind::Tuple(a), TypeKind::Tuple(b)) => {
        let mut idx = 0;
        loop {
          let Some(a_elem) = a.get(idx) else {
            return a.len().cmp(&b.len());
          };
          let Some(b_elem) = b.get(idx) else {
            return a.len().cmp(&b.len());
          };
          let ord = self
            .type_cmp(a_elem.ty, b_elem.ty)
            .then_with(|| a_elem.optional.cmp(&b_elem.optional))
            .then_with(|| a_elem.rest.cmp(&b_elem.rest))
            .then_with(|| a_elem.readonly.cmp(&b_elem.readonly));
          if ord != Ordering::Equal {
            return ord;
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
    }
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
        .then_with(|| self.type_cmp(a_param.ty, b_param.ty))
        .then_with(|| self.compare_param_names(a_param.name, b_param.name));
      if ord != Ordering::Equal {
        return ord;
      }
      idx += 1;
    }
  }

  fn compare_param_names(&self, a: Option<NameId>, b: Option<NameId>) -> Ordering {
    match (a, b) {
      (Some(a), Some(b)) => self.name(a).cmp(&self.name(b)),
      (None, None) => Ordering::Equal,
      (Some(_), None) => Ordering::Greater,
      (None, Some(_)) => Ordering::Less,
    }
  }

  fn compare_type_params(&self, a: &[TypeParamId], b: &[TypeParamId]) -> Ordering {
    let mut idx = 0;
    loop {
      let Some(a_param) = a.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let Some(b_param) = b.get(idx) else {
        return a.len().cmp(&b.len());
      };
      let ord = a_param.cmp(b_param);
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
    let ord = a.key.cmp_with(&b.key, &|id| names.name(id).to_owned());
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
  pub fn debug_json(&self, ty: TypeId) -> serde_json::Value {
    use serde_json::json;
    match self.type_kind(ty) {
      TypeKind::Any => json!({ "kind": "any" }),
      TypeKind::Unknown => json!({ "kind": "unknown" }),
      TypeKind::Never => json!({ "kind": "never" }),
      TypeKind::Void => json!({ "kind": "void" }),
      TypeKind::Null => json!({ "kind": "null" }),
      TypeKind::Undefined => json!({ "kind": "undefined" }),
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
        json!({ "kind": "union", "members": members.iter().map(|m| m.0).collect::<Vec<_>>() })
      }
      TypeKind::Intersection(members) => {
        json!({ "kind": "intersection", "members": members.iter().map(|m| m.0).collect::<Vec<_>>() })
      }
      TypeKind::Object(obj) => {
        let shape = self.object(obj).shape;
        json!({ "kind": "object", "shape": shape.0 })
      }
      TypeKind::Callable { overloads } => {
        json!({ "kind": "callable", "overloads": overloads.iter().map(|o| o.0).collect::<Vec<_>>() })
      }
      TypeKind::Ref { def, args } => {
        json!({ "kind": "ref", "def": def.0, "args": args.iter().map(|a| a.0).collect::<Vec<_>>() })
      }
      TypeKind::This => json!({ "kind": "this" }),
      TypeKind::Infer(param) => json!({ "kind": "infer", "param": param.0 }),
      TypeKind::Tuple(elems) => json!({
        "kind": "tuple",
        "elems": elems.iter().map(|e| json!({
          "ty": e.ty.0,
          "optional": e.optional,
          "rest": e.rest,
          "readonly": e.readonly,
        })).collect::<Vec<_>>(),
      }),
      TypeKind::Array { ty, readonly } => {
        json!({ "kind": "array", "ty": ty.0, "readonly": readonly })
      }
      TypeKind::TypeParam(id) => json!({ "kind": "type_param", "id": id.0 }),
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        distributive,
      } => json!({
        "kind": "conditional",
        "check": check.0,
        "extends": extends.0,
        "true": true_ty.0,
        "false": false_ty.0,
        "distributive": distributive,
      }),
      TypeKind::Mapped(mapped) => json!({
        "kind": "mapped",
        "param": mapped.param.0,
        "source": mapped.source.0,
        "value": mapped.value.0,
        "readonly": format!("{:?}", mapped.readonly),
        "optional": format!("{:?}", mapped.optional),
        "name_type": mapped.name_type.map(|t| t.0),
        "as_type": mapped.as_type.map(|t| t.0),
      }),
      TypeKind::TemplateLiteral(tpl) => json!({
        "kind": "template",
        "head": tpl.head,
        "spans": tpl.spans.iter().map(|s| json!({"literal": s.literal, "ty": s.ty.0})).collect::<Vec<_>>()
      }),
      TypeKind::IndexedAccess { obj, index } => {
        json!({ "kind": "indexed", "obj": obj.0, "index": index.0 })
      }
      TypeKind::KeyOf(inner) => json!({ "kind": "keyof", "ty": inner.0 }),
    }
  }
}
