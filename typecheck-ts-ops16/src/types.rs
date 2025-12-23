use std::collections::BTreeMap;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TypeId(pub u32);

impl TypeId {
  pub fn idx(self) -> usize {
    self.0 as usize
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TemplatePart {
  Literal(String),
  Type(TypeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MappedModifier {
  Inherit,
  Add,
  Remove,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Property {
  pub ty: TypeId,
  pub optional: bool,
  pub readonly: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ObjectType {
  pub properties: BTreeMap<String, Property>,
}

impl ObjectType {
  pub fn new() -> Self {
    Self {
      properties: BTreeMap::new(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MappedType {
  pub param: TypeId,
  pub keys: TypeId,
  pub value_type: TypeId,
  pub as_type: Option<TypeId>,
  pub optional: MappedModifier,
  pub readonly: MappedModifier,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TemplateType {
  pub parts: Vec<TemplatePart>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeKind {
  Any,
  Unknown,
  Never,
  Boolean,
  True,
  False,
  Number,
  String,
  LiteralString(String),
  LiteralNumber(i64),
  TypeParam {
    id: u32,
    name: String,
  },
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  Object(ObjectType),
  Conditional {
    check_type: TypeId,
    extends_type: TypeId,
    true_type: TypeId,
    false_type: TypeId,
    check_param: Option<TypeId>,
  },
  IndexedAccess {
    object: TypeId,
    index: TypeId,
  },
  KeyOf(TypeId),
  Mapped(MappedType),
  Template(TemplateType),
}

pub struct TypeStore {
  types: Vec<TypeKind>,
  intern: HashMap<TypeKind, TypeId>,
  next_type_param: u32,
  any: TypeId,
  unknown: TypeId,
  never: TypeId,
  boolean: TypeId,
  true_ty: TypeId,
  false_ty: TypeId,
  number: TypeId,
  string: TypeId,
}

impl TypeStore {
  pub fn new() -> Self {
    let mut store = TypeStore {
      types: Vec::new(),
      intern: HashMap::new(),
      next_type_param: 0,
      any: TypeId(0),
      unknown: TypeId(0),
      never: TypeId(0),
      boolean: TypeId(0),
      true_ty: TypeId(0),
      false_ty: TypeId(0),
      number: TypeId(0),
      string: TypeId(0),
    };

    store.any = store.intern(TypeKind::Any);
    store.unknown = store.intern(TypeKind::Unknown);
    store.never = store.intern(TypeKind::Never);
    store.boolean = store.intern(TypeKind::Boolean);
    store.true_ty = store.intern(TypeKind::True);
    store.false_ty = store.intern(TypeKind::False);
    store.number = store.intern(TypeKind::Number);
    store.string = store.intern(TypeKind::String);
    store
  }

  pub fn kind(&self, id: TypeId) -> &TypeKind {
    &self.types[id.idx()]
  }

  pub fn any(&self) -> TypeId {
    self.any
  }

  pub fn unknown(&self) -> TypeId {
    self.unknown
  }

  pub fn never(&self) -> TypeId {
    self.never
  }

  pub fn boolean(&self) -> TypeId {
    self.boolean
  }

  pub fn true_type(&self) -> TypeId {
    self.true_ty
  }

  pub fn false_type(&self) -> TypeId {
    self.false_ty
  }

  pub fn number(&self) -> TypeId {
    self.number
  }

  pub fn string(&self) -> TypeId {
    self.string
  }

  pub fn type_param(&mut self, name: impl Into<String>) -> TypeId {
    let id = self.next_type_param;
    self.next_type_param += 1;
    self.intern(TypeKind::TypeParam {
      id,
      name: name.into(),
    })
  }

  pub fn literal_string(&mut self, value: impl Into<String>) -> TypeId {
    self.intern(TypeKind::LiteralString(value.into()))
  }

  pub fn literal_number(&mut self, value: i64) -> TypeId {
    self.intern(TypeKind::LiteralNumber(value))
  }

  pub fn object(&mut self, props: impl IntoIterator<Item = (String, Property)>) -> TypeId {
    let mut map = BTreeMap::new();
    for (k, v) in props {
      map.insert(k, v);
    }
    self.intern(TypeKind::Object(ObjectType { properties: map }))
  }

  pub fn conditional(
    &mut self,
    check_type: TypeId,
    extends_type: TypeId,
    true_type: TypeId,
    false_type: TypeId,
    check_param: Option<TypeId>,
  ) -> TypeId {
    self.intern(TypeKind::Conditional {
      check_type,
      extends_type,
      true_type,
      false_type,
      check_param,
    })
  }

  pub fn indexed_access(&mut self, object: TypeId, index: TypeId) -> TypeId {
    self.intern(TypeKind::IndexedAccess { object, index })
  }

  pub fn keyof(&mut self, target: TypeId) -> TypeId {
    self.intern(TypeKind::KeyOf(target))
  }

  pub fn mapped(
    &mut self,
    param: TypeId,
    keys: TypeId,
    value_type: TypeId,
    as_type: Option<TypeId>,
    optional: MappedModifier,
    readonly: MappedModifier,
  ) -> TypeId {
    self.intern(TypeKind::Mapped(MappedType {
      param,
      keys,
      value_type,
      as_type,
      optional,
      readonly,
    }))
  }

  pub fn template(&mut self, parts: Vec<TemplatePart>) -> TypeId {
    self.intern(TypeKind::Template(TemplateType { parts }))
  }

  pub fn union(&mut self, members: Vec<TypeId>) -> TypeId {
    self.canonical_union(members)
  }

  pub fn intersection(&mut self, members: Vec<TypeId>) -> TypeId {
    self.canonical_intersection(members)
  }

  fn canonical_union(&mut self, members: Vec<TypeId>) -> TypeId {
    let mut flat = Vec::new();
    for m in members {
      match self.kind(m) {
        TypeKind::Union(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(m),
      }
    }

    if flat.iter().any(|m| *m == self.any) {
      return self.any;
    }

    flat.retain(|m| *m != self.never);

    flat.sort_by_key(|m| m.0);
    flat.dedup();

    match flat.len() {
      0 => self.never,
      1 => flat[0],
      _ => self.intern(TypeKind::Union(flat)),
    }
  }

  fn canonical_intersection(&mut self, members: Vec<TypeId>) -> TypeId {
    let mut flat = Vec::new();
    for m in members {
      match self.kind(m) {
        TypeKind::Intersection(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(m),
      }
    }

    if flat.iter().any(|m| *m == self.never) {
      return self.never;
    }

    flat.retain(|m| *m != self.unknown && *m != self.any);

    flat.sort_by_key(|m| m.0);
    flat.dedup();

    match flat.len() {
      0 => self.unknown,
      1 => flat[0],
      _ => self.intern(TypeKind::Intersection(flat)),
    }
  }

  fn intern(&mut self, kind: TypeKind) -> TypeId {
    if let Some(id) = self.intern.get(&kind) {
      return *id;
    }
    let id = TypeId(self.types.len() as u32);
    self.types.push(kind.clone());
    self.intern.insert(kind, id);
    id
  }
}
