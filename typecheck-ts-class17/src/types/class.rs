use super::FunctionType;
use super::IndexKind;
use super::Type;
use crate::types::ClassId;
use std::collections::BTreeMap;

/// Access modifier for class members.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Accessibility {
  Public,
  Protected,
  Private,
}

/// Constructor parameter that optionally declares a property.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstructorParam {
  pub name: String,
  pub ty: Type,
  pub property: Option<Accessibility>,
  pub optional: bool,
  pub definite: bool,
}

impl ConstructorParam {
  pub fn new(name: impl Into<String>, ty: Type) -> Self {
    Self {
      name: name.into(),
      ty,
      property: None,
      optional: false,
      definite: false,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constructor {
  pub params: Vec<ConstructorParam>,
  /// Names of properties written inside the constructor body.
  pub assigns: Vec<String>,
}

impl Constructor {
  pub fn new(params: Vec<ConstructorParam>) -> Self {
    Self {
      params,
      assigns: Vec::new(),
    }
  }
}

/// Class field/variable declaration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassField {
  pub name: String,
  pub ty: Type,
  pub accessibility: Accessibility,
  pub optional: bool,
  pub definite: bool,
  pub has_initializer: bool,
  pub is_static: bool,
}

impl ClassField {
  pub fn new(name: impl Into<String>, ty: Type) -> Self {
    Self {
      name: name.into(),
      ty,
      accessibility: Accessibility::Public,
      optional: false,
      definite: false,
      has_initializer: false,
      is_static: false,
    }
  }
}

/// Method declaration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassMethod {
  pub name: String,
  pub function: FunctionType,
  pub accessibility: Accessibility,
  pub optional: bool,
  pub is_static: bool,
}

impl ClassMethod {
  pub fn new(name: impl Into<String>, function: FunctionType) -> Self {
    Self {
      name: name.into(),
      function,
      accessibility: Accessibility::Public,
      optional: false,
      is_static: false,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassGetter {
  pub name: String,
  pub ty: Type,
  pub accessibility: Accessibility,
  pub is_static: bool,
}

impl ClassGetter {
  pub fn new(name: impl Into<String>, ty: Type) -> Self {
    Self {
      name: name.into(),
      ty,
      accessibility: Accessibility::Public,
      is_static: false,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassSetter {
  pub name: String,
  pub ty: Type,
  pub accessibility: Accessibility,
  pub is_static: bool,
}

impl ClassSetter {
  pub fn new(name: impl Into<String>, ty: Type) -> Self {
    Self {
      name: name.into(),
      ty,
      accessibility: Accessibility::Public,
      is_static: false,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassIndexSignature {
  pub kind: IndexKind,
  pub ty: Type,
  pub is_static: bool,
}

impl ClassIndexSignature {
  pub fn new(kind: IndexKind, ty: Type) -> Self {
    Self {
      kind,
      ty,
      is_static: false,
    }
  }
}

/// Members that may appear on the class body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClassMember {
  Field(ClassField),
  Method(ClassMethod),
  Getter(ClassGetter),
  Setter(ClassSetter),
  IndexSignature(ClassIndexSignature),
}

impl ClassMember {
  pub fn is_static(&self) -> bool {
    matches!(
      self,
      ClassMember::Field(ClassField {
        is_static: true,
        ..
      }) | ClassMember::Method(ClassMethod {
        is_static: true,
        ..
      }) | ClassMember::Getter(ClassGetter {
        is_static: true,
        ..
      }) | ClassMember::Setter(ClassSetter {
        is_static: true,
        ..
      }) | ClassMember::IndexSignature(ClassIndexSignature {
        is_static: true,
        ..
      })
    )
  }
}

/// Helper to differentiate the member's declared form when computing
/// initialization diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ClassMemberKind {
  Field,
  Method,
  Getter,
  Setter,
  Indexer,
  ParameterProperty,
}

/// Class declaration used by the lightweight checker. This is intentionally
/// simple and is constructed directly by tests rather than being parsed from
/// source text.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassDef {
  pub name: String,
  pub extends: Option<ClassId>,
  pub implements: Vec<Type>,
  pub constructor: Option<Constructor>,
  pub members: Vec<ClassMember>,
}

impl ClassDef {
  pub fn new(name: impl Into<String>) -> Self {
    Self {
      name: name.into(),
      extends: None,
      implements: Vec::new(),
      constructor: None,
      members: Vec::new(),
    }
  }
}

/// Member as part of the computed class type (after inheritance and parameter
/// property expansion).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassMemberInfo {
  pub name: String,
  pub ty: Type,
  pub accessibility: Accessibility,
  pub declared_in: ClassId,
  pub optional: bool,
  pub kind: ClassMemberKind,
}

impl ClassMemberInfo {
  pub fn from_field(
    name: String,
    ty: Type,
    accessibility: Accessibility,
    declared_in: ClassId,
    optional: bool,
  ) -> Self {
    Self {
      name,
      ty,
      accessibility,
      declared_in,
      optional,
      kind: ClassMemberKind::Field,
    }
  }
}

/// Aggregated class members and index signatures for both instance and static
/// sides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassInfo {
  pub id: ClassId,
  pub name: String,
  pub extends: Option<ClassId>,
  pub instance_members: BTreeMap<String, ClassMemberInfo>,
  pub static_members: BTreeMap<String, ClassMemberInfo>,
  pub instance_string_index: Option<ClassMemberInfo>,
  pub instance_number_index: Option<ClassMemberInfo>,
  pub static_string_index: Option<ClassMemberInfo>,
  pub static_number_index: Option<ClassMemberInfo>,
}

impl ClassInfo {
  pub fn new(id: ClassId, name: String, extends: Option<ClassId>) -> Self {
    Self {
      id,
      name,
      extends,
      instance_members: BTreeMap::new(),
      static_members: BTreeMap::new(),
      instance_string_index: None,
      instance_number_index: None,
      static_string_index: None,
      static_number_index: None,
    }
  }

  pub fn inherit(&mut self, base: &ClassInfo) {
    self.instance_members.extend(base.instance_members.clone());
    self.static_members.extend(base.static_members.clone());
    if self.instance_string_index.is_none() {
      self.instance_string_index = base.instance_string_index.clone();
    }
    if self.instance_number_index.is_none() {
      self.instance_number_index = base.instance_number_index.clone();
    }
    if self.static_string_index.is_none() {
      self.static_string_index = base.static_string_index.clone();
    }
    if self.static_number_index.is_none() {
      self.static_number_index = base.static_number_index.clone();
    }
  }
}
