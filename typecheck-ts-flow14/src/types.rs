use std::collections::BTreeMap;
use std::fmt;

/// A simplified representation of TypeScript types used by the local flow engine.
///
/// The intent is not to be exhaustive; it only needs to support the narrowing
/// scenarios covered by the tests in this crate. The lattice is intentionally
/// small and canonicalised to make merging deterministic.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Type {
  atoms: Vec<SimpleType>,
}

impl Type {
  pub fn never() -> Self {
    Self { atoms: Vec::new() }
  }

  pub fn any() -> Self {
    Self {
      atoms: vec![SimpleType::Any],
    }
  }

  pub fn unknown() -> Self {
    Self {
      atoms: vec![SimpleType::Unknown],
    }
  }

  pub fn boolean() -> Self {
    Self::from_atom(SimpleType::Boolean)
  }

  pub fn string() -> Self {
    Self::from_atom(SimpleType::String)
  }

  pub fn number() -> Self {
    Self::from_atom(SimpleType::Number)
  }

  pub fn null() -> Self {
    Self::from_atom(SimpleType::Null)
  }

  pub fn undefined() -> Self {
    Self::from_atom(SimpleType::Undefined)
  }

  pub fn boolean_literal(value: bool) -> Self {
    Self::from_atom(SimpleType::BooleanLit(value))
  }

  pub fn string_literal(value: impl Into<String>) -> Self {
    Self::from_atom(SimpleType::StringLit(value.into()))
  }

  pub fn number_literal(value: i64) -> Self {
    Self::from_atom(SimpleType::NumberLit(value))
  }

  pub fn object(object: ObjectType) -> Self {
    Self::from_atom(SimpleType::Object(object))
  }

  pub fn from_atom(atom: SimpleType) -> Self {
    let mut atoms = vec![atom];
    canonicalize_atoms(&mut atoms);
    Self { atoms }
  }

  pub fn is_never(&self) -> bool {
    self.atoms.is_empty()
  }

  pub fn is_any(&self) -> bool {
    self.atoms.iter().any(|a| matches!(a, SimpleType::Any))
  }

  pub fn atoms(&self) -> &[SimpleType] {
    &self.atoms
  }

  /// Union two types, maintaining canonical order and deduplication.
  pub fn union(&self, other: &Self) -> Self {
    if self.is_any() || other.is_any() {
      return Type::any();
    }
    if self.is_never() {
      return other.clone();
    }
    if other.is_never() {
      return self.clone();
    }

    let mut atoms = self.atoms.clone();
    atoms.extend(other.atoms.iter().cloned());
    canonicalize_atoms(&mut atoms);
    Self { atoms }
  }

  /// Intersection of two types. `any` acts as identity; `never` as empty.
  pub fn intersect(&self, other: &Self) -> Self {
    if self.is_any() {
      return other.clone();
    }
    if other.is_any() {
      return self.clone();
    }
    if self.is_never() || other.is_never() {
      return Type::never();
    }

    let atoms = self
      .atoms
      .iter()
      .filter(|a| other.atoms.contains(a))
      .cloned()
      .collect();
    Self { atoms }
  }

  /// Remove atoms that match `other`. If `self` is `any`, return `any` to avoid
  /// unsound complement calculations.
  pub fn exclude(&self, other: &Self) -> Self {
    if self.is_any() {
      return Type::any();
    }
    if self.is_never() {
      return Type::never();
    }
    if other.is_any() {
      return Type::never();
    }

    let atoms = self
      .atoms
      .iter()
      .filter(|a| !other.atoms.contains(a))
      .cloned()
      .collect();
    Self { atoms }
  }

  pub fn truthy_part(&self) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      match atom {
        SimpleType::Boolean => {
          atoms.push(SimpleType::BooleanLit(true));
        }
        SimpleType::BooleanLit(false) => {}
        SimpleType::NumberLit(v) if *v == 0 => {}
        SimpleType::StringLit(v) if v.is_empty() => {}
        SimpleType::Null | SimpleType::Undefined => {}
        other => atoms.push(other.clone()),
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn falsy_part(&self) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      match atom {
        SimpleType::Boolean => atoms.push(SimpleType::BooleanLit(false)),
        SimpleType::BooleanLit(false) => atoms.push(atom.clone()),
        SimpleType::NumberLit(v) if *v == 0 => atoms.push(atom.clone()),
        SimpleType::StringLit(v) if v.is_empty() => atoms.push(atom.clone()),
        SimpleType::Null | SimpleType::Undefined => atoms.push(atom.clone()),
        _ => {}
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn narrow_by_typeof(&self, tag: &str) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      let matches = match (tag, atom) {
        ("string", SimpleType::String | SimpleType::StringLit(_)) => true,
        ("number", SimpleType::Number | SimpleType::NumberLit(_)) => true,
        ("boolean", SimpleType::Boolean | SimpleType::BooleanLit(_)) => true,
        ("undefined", SimpleType::Undefined) => true,
        ("object", SimpleType::Object(_) | SimpleType::Null) => true,
        ("function", SimpleType::Function) => true,
        _ => false,
      };
      if matches {
        atoms.push(atom.clone());
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn exclude_typeof(&self, tag: &str) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      let matches = match (tag, atom) {
        ("string", SimpleType::String | SimpleType::StringLit(_)) => true,
        ("number", SimpleType::Number | SimpleType::NumberLit(_)) => true,
        ("boolean", SimpleType::Boolean | SimpleType::BooleanLit(_)) => true,
        ("undefined", SimpleType::Undefined) => true,
        ("object", SimpleType::Object(_) | SimpleType::Null) => true,
        ("function", SimpleType::Function) => true,
        _ => false,
      };
      if !matches {
        atoms.push(atom.clone());
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn narrow_by_instanceof(&self, class_name: &str) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      match atom {
        SimpleType::Object(obj) if obj.class.as_deref() == Some(class_name) => {
          atoms.push(atom.clone())
        }
        SimpleType::Class(name) if name == class_name => atoms.push(atom.clone()),
        _ => {}
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn narrow_by_property(&self, property: &str) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      match atom {
        SimpleType::Object(obj) if obj.props.contains_key(property) => atoms.push(atom.clone()),
        _ => {}
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn narrow_by_discriminant(&self, property: &str, value: &str) -> Self {
    if self.is_any() {
      return Type::any();
    }
    let mut atoms = Vec::new();
    for atom in &self.atoms {
      match atom {
        SimpleType::Object(obj) => {
          if let Some(prop_ty) = obj.props.get(property) {
            if prop_ty
              .atoms
              .iter()
              .any(|p| matches!(p, SimpleType::StringLit(v) if v == value))
            {
              atoms.push(atom.clone());
            }
          }
        }
        _ => {}
      }
    }
    canonicalize_atoms(&mut atoms);
    Type { atoms }
  }

  pub fn property_type(&self, property: &str) -> Type {
    if self.is_any() {
      return Type::any();
    }
    let mut result = Type::never();
    for atom in &self.atoms {
      match atom {
        SimpleType::Object(obj) => {
          if let Some(prop_ty) = obj.props.get(property) {
            result = result.union(prop_ty);
          }
        }
        _ => {}
      }
    }
    result
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.is_any() {
      return write!(f, "any");
    }
    if self.is_never() {
      return write!(f, "never");
    }
    let mut first = true;
    for atom in &self.atoms {
      if !first {
        write!(f, " | ")?;
      }
      first = false;
      write!(f, "{atom}")?;
    }
    Ok(())
  }
}

fn canonicalize_atoms(atoms: &mut Vec<SimpleType>) {
  atoms.sort();
  atoms.dedup();
  if atoms.iter().any(|a| matches!(a, SimpleType::Any)) {
    atoms.clear();
    atoms.push(SimpleType::Any);
  }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleType {
  Any,
  Unknown,
  Boolean,
  BooleanLit(bool),
  Number,
  NumberLit(i64),
  String,
  StringLit(String),
  Null,
  Undefined,
  /// Represents callable function values when needed for typeof checks.
  Function,
  /// Structural object type with optional class name for instanceof narrowing.
  Object(ObjectType),
  /// Nominal class-like token for instanceof narrowing when not using ObjectType.
  Class(String),
}

impl fmt::Display for SimpleType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      SimpleType::Any => write!(f, "any"),
      SimpleType::Unknown => write!(f, "unknown"),
      SimpleType::Boolean => write!(f, "boolean"),
      SimpleType::BooleanLit(v) => write!(f, "{}", v),
      SimpleType::Number => write!(f, "number"),
      SimpleType::NumberLit(v) => write!(f, "{v}"),
      SimpleType::String => write!(f, "string"),
      SimpleType::StringLit(v) => write!(f, "\"{v}\""),
      SimpleType::Null => write!(f, "null"),
      SimpleType::Undefined => write!(f, "undefined"),
      SimpleType::Function => write!(f, "function"),
      SimpleType::Object(obj) => write!(f, "{}", obj),
      SimpleType::Class(name) => write!(f, "{name}"),
    }
  }
}

/// Simplified object representation used by narrowing. Properties are stored as
/// plain types; class is used to model `instanceof` checks.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjectType {
  pub class: Option<String>,
  pub props: BTreeMap<String, Type>,
}

impl ObjectType {
  pub fn new(class: Option<String>, props: BTreeMap<String, Type>) -> Self {
    Self { class, props }
  }

  pub fn with_prop(mut self, name: impl Into<String>, ty: Type) -> Self {
    self.props.insert(name.into(), ty);
    self
  }
}

impl fmt::Display for ObjectType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{{")?;
    let mut first = true;
    for (k, v) in &self.props {
      if !first {
        write!(f, ", ")?;
      }
      first = false;
      write!(f, "{k}: {v}")?;
    }
    write!(f, "}}")
  }
}
