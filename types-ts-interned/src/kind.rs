use crate::ids::DefId;
use crate::ids::NameId;
use crate::ids::ObjectId;
use crate::ids::SignatureId;
use crate::ids::TypeId;
use crate::ids::TypeParamId;
use crate::shape::Shape;
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum MappedModifier {
  Add,
  Remove,
  Preserve,
}

impl Default for MappedModifier {
  fn default() -> Self {
    Self::Preserve
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MappedType {
  pub param: TypeParamId,
  pub source: TypeId,
  pub value: TypeId,
  pub readonly: MappedModifier,
  pub optional: MappedModifier,
  pub name_type: Option<TypeId>,
  pub as_type: Option<TypeId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TemplateLiteralType {
  pub head: String,
  pub spans: Vec<TemplateChunk>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TemplateChunk {
  pub literal: String,
  pub ty: TypeId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypeKind {
  Any,
  Unknown,
  Never,
  Void,
  Null,
  Undefined,
  Boolean,
  Number,
  String,
  BigInt,
  Symbol,
  UniqueSymbol,
  BooleanLiteral(bool),
  NumberLiteral(OrderedFloat<f64>),
  StringLiteral(NameId),
  BigIntLiteral(BigInt),
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  Object(ObjectId),
  Callable {
    overloads: Vec<SignatureId>,
  },
  Ref {
    def: DefId,
    args: Vec<TypeId>,
  },
  TypeParam(TypeParamId),
  Conditional {
    check: TypeId,
    extends: TypeId,
    true_ty: TypeId,
    false_ty: TypeId,
    distributive: bool,
  },
  Mapped(MappedType),
  TemplateLiteral(TemplateLiteralType),
  IndexedAccess {
    obj: TypeId,
    index: TypeId,
  },
  KeyOf(TypeId),
}

impl TypeKind {
  pub(crate) fn discriminant(&self) -> u8 {
    match self {
      TypeKind::Any => 0,
      TypeKind::Unknown => 1,
      TypeKind::Never => 2,
      TypeKind::Void => 3,
      TypeKind::Null => 4,
      TypeKind::Undefined => 5,
      TypeKind::Boolean => 6,
      TypeKind::Number => 7,
      TypeKind::String => 8,
      TypeKind::BigInt => 9,
      TypeKind::Symbol => 10,
      TypeKind::UniqueSymbol => 11,
      TypeKind::BooleanLiteral(_) => 12,
      TypeKind::NumberLiteral(_) => 13,
      TypeKind::StringLiteral(_) => 14,
      TypeKind::BigIntLiteral(_) => 15,
      TypeKind::Union(_) => 16,
      TypeKind::Intersection(_) => 17,
      TypeKind::Object(_) => 18,
      TypeKind::Callable { .. } => 19,
      TypeKind::Ref { .. } => 20,
      TypeKind::TypeParam(_) => 21,
      TypeKind::Conditional { .. } => 22,
      TypeKind::Mapped(_) => 23,
      TypeKind::TemplateLiteral(_) => 24,
      TypeKind::IndexedAccess { .. } => 25,
      TypeKind::KeyOf(_) => 26,
    }
  }
}

/// Helper used for stable ordering when canonicalizing complex composite types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompositeKind<'a> {
  Union(&'a [TypeId]),
  Intersection(&'a [TypeId]),
  Object(&'a Shape),
}
