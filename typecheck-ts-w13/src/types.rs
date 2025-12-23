use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LiteralType {
  String(String),
  Number(String),
  Boolean(bool),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType {
  pub params: Vec<TypeId>,
  pub return_type: TypeId,
  pub constructable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
  Any,
  Unknown,
  Never,
  Void,
  Number,
  String,
  Boolean,
  Null,
  Undefined,
  Object(BTreeMap<String, TypeId>),
  Array(TypeId),
  Function(FunctionType),
  Union(Vec<TypeId>),
  Literal(LiteralType),
}

/// Simple type store with interning.
pub struct TypeStore {
  types: Vec<Type>,
  map: HashMap<Type, TypeId>,
  any: TypeId,
  unknown: TypeId,
  never: TypeId,
  void: TypeId,
  number: TypeId,
  string: TypeId,
  boolean: TypeId,
  null: TypeId,
  undefined: TypeId,
}

impl Default for TypeStore {
  fn default() -> Self {
    Self::new()
  }
}

impl TypeStore {
  pub fn new() -> Self {
    let mut store = TypeStore {
      types: Vec::new(),
      map: HashMap::new(),
      any: TypeId(0),
      unknown: TypeId(0),
      never: TypeId(0),
      void: TypeId(0),
      number: TypeId(0),
      string: TypeId(0),
      boolean: TypeId(0),
      null: TypeId(0),
      undefined: TypeId(0),
    };

    store.any = store.intern(Type::Any);
    store.unknown = store.intern(Type::Unknown);
    store.never = store.intern(Type::Never);
    store.void = store.intern(Type::Void);
    store.number = store.intern(Type::Number);
    store.string = store.intern(Type::String);
    store.boolean = store.intern(Type::Boolean);
    store.null = store.intern(Type::Null);
    store.undefined = store.intern(Type::Undefined);

    store
  }

  pub fn intern(&mut self, ty: Type) -> TypeId {
    if let Some(id) = self.map.get(&ty) {
      return *id;
    }
    let id = TypeId(self.types.len());
    self.types.push(ty.clone());
    self.map.insert(ty, id);
    id
  }

  pub fn get(&self, id: TypeId) -> &Type {
    &self.types[id.0]
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

  pub fn void(&self) -> TypeId {
    self.void
  }

  pub fn number(&self) -> TypeId {
    self.number
  }

  pub fn string(&self) -> TypeId {
    self.string
  }

  pub fn boolean(&self) -> TypeId {
    self.boolean
  }

  pub fn null(&self) -> TypeId {
    self.null
  }

  pub fn undefined(&self) -> TypeId {
    self.undefined
  }

  pub fn union(&mut self, mut members: Vec<TypeId>) -> TypeId {
    let mut flat = Vec::new();
    for member in members.drain(..) {
      match self.get(member) {
        Type::Union(inner) => flat.extend(inner.iter().copied()),
        _ => flat.push(member),
      }
    }
    flat.sort();
    flat.dedup();
    if flat.len() == 1 {
      return flat[0];
    }
    self.intern(Type::Union(flat))
  }

  pub fn array(&mut self, elem: TypeId) -> TypeId {
    self.intern(Type::Array(elem))
  }

  pub fn function(
    &mut self,
    params: Vec<TypeId>,
    return_type: TypeId,
    constructable: bool,
  ) -> TypeId {
    self.intern(Type::Function(FunctionType {
      params,
      return_type,
      constructable,
    }))
  }

  pub fn object(&mut self, props: BTreeMap<String, TypeId>) -> TypeId {
    self.intern(Type::Object(props))
  }

  pub fn literal_string(&mut self, value: impl Into<String>) -> TypeId {
    self.intern(Type::Literal(LiteralType::String(value.into())))
  }

  pub fn literal_number(&mut self, value: impl Into<String>) -> TypeId {
    self.intern(Type::Literal(LiteralType::Number(value.into())))
  }

  pub fn literal_bool(&mut self, value: bool) -> TypeId {
    self.intern(Type::Literal(LiteralType::Boolean(value)))
  }

  pub fn widen(&mut self, ty: TypeId) -> TypeId {
    match self.get(ty) {
      Type::Literal(LiteralType::String(_)) => self.string(),
      Type::Literal(LiteralType::Number(_)) => self.number(),
      Type::Literal(LiteralType::Boolean(_)) => self.boolean(),
      _ => ty,
    }
  }

  /// Simplified assignability relation suitable for early-stage checking.
  pub fn is_assignable(&mut self, source: TypeId, target: TypeId) -> bool {
    if source == target {
      return true;
    }
    if target == self.any() || source == self.never() || source == self.any() {
      return true;
    }
    if target == self.unknown() {
      return true;
    }
    if source == self.unknown() {
      return false;
    }
    let source_ty = self.get(source).clone();
    let target_ty = self.get(target).clone();

    match (source_ty, target_ty) {
      (_, Type::Union(targets)) => {
        for t in targets {
          if self.is_assignable(source, t) {
            return true;
          }
        }
        false
      }
      (Type::Union(sources), _) => {
        for s in sources {
          if !self.is_assignable(s, target) {
            return false;
          }
        }
        true
      }
      (Type::Array(src_elem), Type::Array(dst_elem)) => self.is_assignable(src_elem, dst_elem),
      (Type::Object(src_props), Type::Object(dst_props)) => {
        for (name, dst_ty) in dst_props.iter() {
          match src_props.get(name) {
            Some(src_ty) if self.is_assignable(*src_ty, *dst_ty) => {}
            _ => return false,
          }
        }
        true
      }
      (Type::Function(src_fn), Type::Function(dst_fn)) => {
        if src_fn.params.len() != dst_fn.params.len() {
          return false;
        }
        for (s, t) in src_fn.params.iter().zip(dst_fn.params.iter()) {
          if !self.is_assignable(*t, *s) {
            return false;
          }
        }
        self.is_assignable(src_fn.return_type, dst_fn.return_type)
      }
      (Type::Literal(_), other) => {
        let widened = self.widen(source);
        self.is_assignable(widened, target) || matches!(other, Type::Any)
      }
      (other, Type::Literal(_)) => {
        let widened = self.widen(target);
        self.is_assignable(source, widened) || matches!(other, Type::Any)
      }
      _ => false,
    }
  }
}

pub struct TypeDisplay<'a> {
  store: &'a TypeStore,
  ty: TypeId,
}

impl<'a> TypeDisplay<'a> {
  pub fn new(store: &'a TypeStore, ty: TypeId) -> Self {
    TypeDisplay { store, ty }
  }
}

impl<'a> fmt::Display for TypeDisplay<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.store.get(self.ty) {
      Type::Any => write!(f, "any"),
      Type::Unknown => write!(f, "unknown"),
      Type::Never => write!(f, "never"),
      Type::Void => write!(f, "void"),
      Type::Number => write!(f, "number"),
      Type::String => write!(f, "string"),
      Type::Boolean => write!(f, "boolean"),
      Type::Null => write!(f, "null"),
      Type::Undefined => write!(f, "undefined"),
      Type::Array(elem) => write!(f, "{}[]", TypeDisplay::new(self.store, *elem)),
      Type::Union(members) => {
        for (i, member) in members.iter().enumerate() {
          if i > 0 {
            write!(f, " | ")?;
          }
          write!(f, "{}", TypeDisplay::new(self.store, *member))?;
        }
        Ok(())
      }
      Type::Object(props) => {
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in props.iter() {
          if !first {
            write!(f, ", ")?;
          }
          first = false;
          write!(f, "{}: {}", k, TypeDisplay::new(self.store, *v))?;
        }
        write!(f, "}}")
      }
      Type::Function(func) => {
        write!(f, "(")?;
        for (i, param) in func.params.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", TypeDisplay::new(self.store, *param))?;
        }
        write!(f, ") => {}", TypeDisplay::new(self.store, func.return_type))
      }
      Type::Literal(LiteralType::String(v)) => write!(f, "\"{}\"", v),
      Type::Literal(LiteralType::Number(v)) => write!(f, "{}", v),
      Type::Literal(LiteralType::Boolean(v)) => write!(f, "{}", v),
    }
  }
}
