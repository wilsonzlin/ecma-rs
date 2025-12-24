use std::collections::HashMap;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeRefId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeKind {
  Any,
  Unknown,
  Never,
  Undefined,
  Null,
  Boolean,
  Number,
  String,
  BigInt,
  Symbol,
  Literal(LiteralType),
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  Object(ObjectType),
  Function(FunctionType),
  Ref(TypeRefId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LiteralType {
  String(String),
  Number(i64),
  Boolean(bool),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ObjectType {
  pub properties: Vec<Property>,
  pub index_signatures: Vec<IndexSignature>,
}

impl ObjectType {
  pub fn new(mut properties: Vec<Property>, mut index_signatures: Vec<IndexSignature>) -> Self {
    properties.sort_by(|a, b| a.name.cmp(&b.name));
    index_signatures.sort_by(|a, b| a.kind.cmp(&b.kind));
    Self {
      properties,
      index_signatures,
    }
  }

  pub fn find_property(&self, name: &str) -> Option<&Property> {
    self
      .properties
      .binary_search_by(|p| p.name.as_str().cmp(name))
      .ok()
      .map(|idx| &self.properties[idx])
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Property {
  pub name: String,
  pub ty: TypeId,
  pub optional: bool,
  pub readonly: bool,
  pub is_method: bool,
  pub visibility: MemberVisibility,
  pub origin_id: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MemberVisibility {
  Public,
  Private,
  Protected,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IndexSignature {
  pub kind: IndexKind,
  pub ty: TypeId,
  pub readonly: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IndexKind {
  String,
  Number,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType {
  pub params: Vec<FnParam>,
  pub ret: TypeId,
  pub is_method: bool,
}

impl FunctionType {
  pub fn required_params(&self) -> usize {
    self
      .params
      .iter()
      .filter(|p| !p.optional && !p.rest)
      .count()
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnParam {
  pub name: Option<String>,
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeOptions {
  pub strict_null_checks: bool,
  pub strict_function_types: bool,
}

impl Default for TypeOptions {
  fn default() -> Self {
    Self {
      strict_null_checks: true,
      strict_function_types: true,
    }
  }
}

pub struct TypeStore {
  types: Vec<TypeKind>,
  interner: HashMap<TypeKind, TypeId>,
  any: TypeId,
  unknown: TypeId,
  never: TypeId,
  undefined: TypeId,
  null: TypeId,
  boolean: TypeId,
  number: TypeId,
  string: TypeId,
}

impl TypeStore {
  pub fn new() -> Self {
    let mut store = TypeStore {
      types: Vec::new(),
      interner: HashMap::new(),
      any: TypeId(0),
      unknown: TypeId(0),
      never: TypeId(0),
      undefined: TypeId(0),
      null: TypeId(0),
      boolean: TypeId(0),
      number: TypeId(0),
      string: TypeId(0),
    };
    store.any = store.intern_raw(TypeKind::Any);
    store.unknown = store.intern_raw(TypeKind::Unknown);
    store.never = store.intern_raw(TypeKind::Never);
    store.undefined = store.intern_raw(TypeKind::Undefined);
    store.null = store.intern_raw(TypeKind::Null);
    store.boolean = store.intern_raw(TypeKind::Boolean);
    store.number = store.intern_raw(TypeKind::Number);
    store.string = store.intern_raw(TypeKind::String);
    store
  }

  fn intern_raw(&mut self, kind: TypeKind) -> TypeId {
    if let Some(id) = self.interner.get(&kind) {
      return *id;
    }
    let id = TypeId(self.types.len() as u32);
    self.types.push(kind.clone());
    self.interner.insert(kind, id);
    id
  }

  pub fn intern(&mut self, kind: TypeKind) -> TypeId {
    let normalized = self.normalize(kind);
    self.intern_raw(normalized)
  }

  fn normalize(&self, kind: TypeKind) -> TypeKind {
    match kind {
      TypeKind::Union(members) => self.normalize_union(members),
      TypeKind::Intersection(members) => self.normalize_intersection(members),
      TypeKind::Object(obj) => {
        let mut obj = obj;
        obj.properties.sort_by(|a, b| a.name.cmp(&b.name));
        obj.index_signatures.sort_by(|a, b| a.kind.cmp(&b.kind));
        TypeKind::Object(obj)
      }
      other => other,
    }
  }

  fn normalize_union(&self, members: Vec<TypeId>) -> TypeKind {
    let mut flat: Vec<TypeId> = Vec::new();
    for m in members {
      match self.get(m) {
        TypeKind::Union(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(m),
      }
    }

    if flat.iter().any(|m| *m == self.any) {
      return TypeKind::Any;
    }
    if flat.iter().any(|m| *m == self.unknown) {
      return TypeKind::Unknown;
    }

    let mut set: Vec<TypeId> = Vec::new();
    for id in flat {
      if *self.get(id) == TypeKind::Never {
        continue;
      }
      if !set.contains(&id) {
        set.push(id);
      }
    }
    set.sort_by_key(|id| id.0);
    if set.is_empty() {
      return TypeKind::Never;
    }
    if set.len() == 1 {
      return self.get(set[0]).clone();
    }
    TypeKind::Union(set)
  }

  fn normalize_intersection(&self, members: Vec<TypeId>) -> TypeKind {
    let mut flat: Vec<TypeId> = Vec::new();
    for m in members {
      match self.get(m) {
        TypeKind::Intersection(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(m),
      }
    }

    if flat.iter().any(|m| *m == self.never) {
      return TypeKind::Never;
    }

    let mut set: Vec<TypeId> = Vec::new();
    for id in flat {
      match self.get(id) {
        TypeKind::Any | TypeKind::Unknown => continue,
        _ => {}
      }
      if !set.contains(&id) {
        set.push(id);
      }
    }
    set.sort_by_key(|id| id.0);
    if set.is_empty() {
      return TypeKind::Unknown;
    }
    if set.len() == 1 {
      return self.get(set[0]).clone();
    }
    TypeKind::Intersection(set)
  }

  pub fn get(&self, id: TypeId) -> &TypeKind {
    &self.types[id.0 as usize]
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

  pub fn undefined(&self) -> TypeId {
    self.undefined
  }

  pub fn null(&self) -> TypeId {
    self.null
  }

  pub fn boolean(&self) -> TypeId {
    self.boolean
  }

  pub fn number(&self) -> TypeId {
    self.number
  }

  pub fn string(&self) -> TypeId {
    self.string
  }

  pub fn literal_string(&mut self, value: impl Into<String>) -> TypeId {
    self.intern(TypeKind::Literal(LiteralType::String(value.into())))
  }

  pub fn literal_number(&mut self, value: i64) -> TypeId {
    self.intern(TypeKind::Literal(LiteralType::Number(value)))
  }

  pub fn literal_boolean(&mut self, value: bool) -> TypeId {
    self.intern(TypeKind::Literal(LiteralType::Boolean(value)))
  }

  pub fn union(&mut self, members: Vec<TypeId>) -> TypeId {
    self.intern(TypeKind::Union(members))
  }

  pub fn intersection(&mut self, members: Vec<TypeId>) -> TypeId {
    self.intern(TypeKind::Intersection(members))
  }

  pub fn object(&mut self, obj: ObjectType) -> TypeId {
    self.intern(TypeKind::Object(obj))
  }

  pub fn function(&mut self, func: FunctionType) -> TypeId {
    self.intern(TypeKind::Function(func))
  }

  pub fn type_ref(&mut self, id: TypeRefId) -> TypeId {
    self.intern(TypeKind::Ref(id))
  }
}
