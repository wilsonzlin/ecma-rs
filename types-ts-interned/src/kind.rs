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
  /// Type parameter used for the mapped key variable.
  pub param: TypeParamId,
  /// Source type from the `in` clause.
  pub source: TypeId,
  /// Value type assigned to each mapped property.
  pub value: TypeId,
  /// Readonly modifier applied to the mapped properties.
  pub readonly: MappedModifier,
  /// Optional modifier applied to the mapped properties.
  pub optional: MappedModifier,
  /// Mirrors TypeScript's internal `nameType` used during key remapping.
  /// This has no distinct surface syntax from `as_type`, so it is retained
  /// for fidelity but intentionally omitted from `TypeDisplay`.
  pub name_type: Option<TypeId>,
  /// Explicit `as` clause used to remap keys.
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum IntrinsicKind {
  Uppercase,
  Lowercase,
  Capitalize,
  Uncapitalize,
  NoInfer,
}

impl IntrinsicKind {
  pub fn from_name(name: &str) -> Option<Self> {
    match name {
      "Uppercase" => Some(Self::Uppercase),
      "Lowercase" => Some(Self::Lowercase),
      "Capitalize" => Some(Self::Capitalize),
      "Uncapitalize" => Some(Self::Uncapitalize),
      "NoInfer" => Some(Self::NoInfer),
      _ => None,
    }
  }

  pub fn as_str(&self) -> &'static str {
    match self {
      Self::Uppercase => "Uppercase",
      Self::Lowercase => "Lowercase",
      Self::Capitalize => "Capitalize",
      Self::Uncapitalize => "Uncapitalize",
      Self::NoInfer => "NoInfer",
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TupleElem {
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
  pub readonly: bool,
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
  This,
  Infer {
    param: TypeParamId,
    constraint: Option<TypeId>,
  },
  Tuple(Vec<TupleElem>),
  Array {
    ty: TypeId,
    readonly: bool,
  },
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  Object(ObjectId),
  Callable {
    overloads: Vec<SignatureId>,
  },
  Ref {
    /// Canonical definition identifier from `hir-js` for the referenced type.
    def: DefId,
    /// Type arguments applied to the referenced definition.
    args: Vec<TypeId>,
  },
  TypeParam(TypeParamId),
  Predicate {
    /// Parameter being tested or asserted, when known.
    parameter: Option<NameId>,
    /// Type asserted when the predicate succeeds. `None` indicates an unknown
    /// asserted type (treated as `boolean`).
    asserted: Option<TypeId>,
    /// Whether the predicate acts as an assertion function (throws on failure).
    asserts: bool,
  },
  Conditional {
    check: TypeId,
    extends: TypeId,
    true_ty: TypeId,
    false_ty: TypeId,
    distributive: bool,
  },
  Mapped(MappedType),
  TemplateLiteral(TemplateLiteralType),
  Intrinsic {
    kind: IntrinsicKind,
    ty: TypeId,
  },
  IndexedAccess {
    obj: TypeId,
    index: TypeId,
  },
  KeyOf(TypeId),
  /// The TypeScript `{}` type literal with no members.
  ///
  /// Semantics:
  /// - With `strictNullChecks: true`: all types except `null` and `undefined`.
  /// - With `strictNullChecks: false`: behaves like the top type (everything).
  ///
  /// This is intentionally distinct from the `object` keyword, which excludes
  /// primitives and is represented separately as an (empty) structural object.
  EmptyObject,
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
      TypeKind::This => 16,
      TypeKind::Infer { .. } => 17,
      TypeKind::Tuple(_) => 18,
      TypeKind::Array { .. } => 19,
      TypeKind::Union(_) => 20,
      TypeKind::Intersection(_) => 21,
      TypeKind::Object(_) => 22,
      TypeKind::Callable { .. } => 23,
      TypeKind::Ref { .. } => 24,
      TypeKind::TypeParam(_) => 25,
      TypeKind::Predicate { .. } => 26,
      TypeKind::Conditional { .. } => 27,
      TypeKind::Mapped(_) => 28,
      TypeKind::TemplateLiteral(_) => 29,
      TypeKind::IndexedAccess { .. } => 30,
      TypeKind::KeyOf(_) => 31,
      TypeKind::EmptyObject => 32,
      TypeKind::Intrinsic { .. } => 33,
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
