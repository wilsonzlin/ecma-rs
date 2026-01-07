use crate::ids::NameId;
use crate::ids::ShapeId;
use crate::ids::SignatureId;
use crate::ids::TypeId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Accessibility {
  Public,
  Protected,
  Private,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PropData {
  pub ty: TypeId,
  pub optional: bool,
  pub readonly: bool,
  pub accessibility: Option<Accessibility>,
  /// Whether this property originated from a method declaration. Methods are
  /// treated with bivariant parameter checking in strict function mode to match
  /// TypeScript's behavior.
  pub is_method: bool,
  /// Optional nominal origin identifier attached to private/protected members.
  /// When present, relation hooks can require the same origin for compatibility.
  pub origin: Option<u32>,
  /// Optional identifier for the declaration that introduced this property.
  /// This can be used by relation hooks to decide if otherwise-incompatible
  /// private members share the same origin.
  pub declared_on: Option<crate::ids::DefId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PropKey {
  String(NameId),
  Number(i64),
  Symbol(NameId),
}

impl PropKey {
  pub(crate) fn cmp_with<'a>(
    &self,
    other: &Self,
    resolve_name: &impl Fn(NameId) -> &'a str,
  ) -> std::cmp::Ordering {
    use PropKey::*;
    let discr = self.discriminant().cmp(&other.discriminant());
    if discr != std::cmp::Ordering::Equal {
      return discr;
    }
    match (self, other) {
      (String(a), String(b)) | (Symbol(a), Symbol(b)) => resolve_name(*a).cmp(resolve_name(*b)),
      (Number(a), Number(b)) => a.cmp(b),
      _ => std::cmp::Ordering::Equal,
    }
  }

  fn discriminant(&self) -> u8 {
    match self {
      PropKey::String(_) => 0,
      PropKey::Number(_) => 1,
      PropKey::Symbol(_) => 2,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Property {
  pub key: PropKey,
  pub data: PropData,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Indexer {
  pub key_type: TypeId,
  pub value_type: TypeId,
  pub readonly: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Shape {
  pub properties: Vec<Property>,
  pub call_signatures: Vec<SignatureId>,
  pub construct_signatures: Vec<SignatureId>,
  pub indexers: Vec<Indexer>,
}

impl Shape {
  pub fn new() -> Self {
    Self {
      properties: Vec::new(),
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      indexers: Vec::new(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ObjectType {
  pub shape: ShapeId,
}
