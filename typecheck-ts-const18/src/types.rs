use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
  Any,
  Never,
  Number,
  String,
  Boolean,
  LiteralNumber(i128),
  LiteralString(String),
  LiteralBoolean(bool),
  Object(Box<ObjectType>),
  Array(Box<Type>),
  Tuple(TupleType),
  Union(Vec<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Property {
  pub name: String,
  pub typ: Type,
  pub optional: bool,
  pub readonly: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IndexSignature {
  pub value: Box<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ObjectType {
  pub properties: Vec<Property>,
  pub index_signature: Option<Box<IndexSignature>>,
}

impl ObjectType {
  pub fn has_property(&self, name: &str) -> bool {
    self.properties.iter().any(|p| p.name == name)
  }

  pub fn property(&self, name: &str) -> Option<&Property> {
    self.properties.iter().find(|p| p.name == name)
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TupleType {
  pub elements: Vec<Type>,
  pub readonly: bool,
}

impl Type {
  pub fn union(mut types: Vec<Type>) -> Type {
    let mut flat: Vec<Type> = Vec::new();
    for t in types.drain(..) {
      match t {
        Type::Union(inner) => flat.extend(inner),
        other => flat.push(other),
      }
    }
    if flat.is_empty() {
      return Type::Never;
    }
    flat.sort_by(|a, b| type_sort_key(a).cmp(&type_sort_key(b)));
    flat.dedup();
    if flat.len() == 1 {
      return flat.pop().unwrap();
    }
    Type::Union(flat)
  }

  pub fn is_literal_string(&self, value: &str) -> bool {
    matches!(self, Type::LiteralString(v) if v == value)
  }

  pub fn is_literal_number(&self, value: i128) -> bool {
    matches!(self, Type::LiteralNumber(v) if *v == value)
  }

  pub fn is_literal_boolean(&self, value: bool) -> bool {
    matches!(self, Type::LiteralBoolean(v) if *v == value)
  }
}

pub fn type_sort_key(typ: &Type) -> String {
  format!("{:?}", typ)
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::Any => write!(f, "any"),
      Type::Never => write!(f, "never"),
      Type::Number => write!(f, "number"),
      Type::String => write!(f, "string"),
      Type::Boolean => write!(f, "boolean"),
      Type::LiteralNumber(n) => write!(f, "{}", n),
      Type::LiteralString(s) => write!(f, "\"{}\"", s),
      Type::LiteralBoolean(b) => write!(f, "{}", b),
      Type::Array(elem) => write!(f, "{}[]", elem),
      Type::Tuple(tuple) => {
        if tuple.readonly {
          write!(f, "readonly ")?;
        }
        write!(f, "[")?;
        for (i, el) in tuple.elements.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", el)?;
        }
        write!(f, "]")
      }
      Type::Object(obj) => {
        write!(f, "{{")?;
        for (i, prop) in obj.properties.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          if prop.readonly {
            write!(f, "readonly ")?;
          }
          write!(f, "{}: {}", prop.name, prop.typ)?;
          if prop.optional {
            write!(f, "?")?;
          }
          if i + 1 != obj.properties.len() {
            write!(f, ";")?;
          }
        }
        if obj.index_signature.is_some() && !obj.properties.is_empty() {
          write!(f, "; ")?;
        }
        if let Some(sig) = &obj.index_signature {
          write!(f, "[key: string]: {}", sig.value)?;
        }
        write!(f, "}}")
      }
      Type::Union(types) => {
        for (i, t) in types.iter().enumerate() {
          if i > 0 {
            write!(f, " | ")?;
          }
          write!(f, "{}", t)?;
        }
        Ok(())
      }
    }
  }
}
