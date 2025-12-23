use std::collections::BTreeMap;

pub mod class;

pub type ClassId = usize;
pub type InterfaceId = usize;

/// A simplified representation of TypeScript types sufficient for the
/// class compatibility checks used in the tests for this crate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
  Any,
  Unknown,
  Never,
  Void,
  Boolean,
  Number,
  String,
  ClassInstance(ClassId),
  ClassStatics(ClassId),
  Interface(InterfaceId),
  Object(ObjectType),
  Function(FunctionType),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ObjectType {
  pub properties: BTreeMap<String, ObjectProperty>,
  pub string_index: Option<Box<Type>>, // type of values for string keys
  pub number_index: Option<Box<Type>>, // type of values for number keys
}

impl ObjectType {
  pub fn new() -> Self {
    Self {
      properties: BTreeMap::new(),
      string_index: None,
      number_index: None,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ObjectProperty {
  pub ty: Type,
  pub optional: bool,
}

/// Function type with optional `this` parameter support.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType {
  pub this_param: Option<Box<Type>>, // Explicit or contextual `this`
  pub params: Vec<Type>,
  pub return_type: Box<Type>,
}

impl FunctionType {
  pub fn new(params: Vec<Type>, return_type: Type) -> Self {
    Self {
      this_param: None,
      params,
      return_type: Box::new(return_type),
    }
  }

  pub fn with_this(mut self, this_ty: Type) -> Self {
    self.this_param = Some(Box::new(this_ty));
    self
  }
}

/// Class or interface index signature kind. Only number/string are needed for
/// the current tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IndexKind {
  String,
  Number,
}

/// Simple interface definition describing structural members.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InterfaceDef {
  pub name: String,
  pub extends: Vec<InterfaceId>,
  pub properties: BTreeMap<String, ObjectProperty>,
  pub string_index: Option<Box<Type>>,
  pub number_index: Option<Box<Type>>,
}

impl InterfaceDef {
  pub fn new(name: impl Into<String>) -> Self {
    Self {
      name: name.into(),
      extends: Vec::new(),
      properties: BTreeMap::new(),
      string_index: None,
      number_index: None,
    }
  }
}
