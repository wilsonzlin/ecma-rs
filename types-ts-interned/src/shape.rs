use crate::ids::NameId;
use crate::ids::ObjectId;
use crate::ids::ShapeId;
use crate::ids::SignatureId;
use crate::ids::TypeId;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum Accessibility {
  Public,
  Protected,
  Private,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PropData {
  pub ty: TypeId,
  pub optional: bool,
  pub readonly: bool,
  pub accessibility: Option<Accessibility>,
  /// Whether this property originated from a method declaration. Methods are
  /// treated with bivariant parameter checking in strict function mode to match
  /// TypeScript's behavior.
  pub is_method: bool,
  /// Optional identifier for the declaration that introduced this property.
  /// This can be used by relation hooks to decide if otherwise-incompatible
  /// private members share the same origin.
  pub declared_on: Option<crate::ids::DefId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PropKey {
  String(NameId),
  Number(i64),
  Symbol(NameId),
}

impl PropKey {
  pub(crate) fn cmp_with(
    &self,
    other: &Self,
    resolve_name: &impl Fn(NameId) -> String,
  ) -> std::cmp::Ordering {
    use PropKey::*;
    let discr = self.discriminant().cmp(&other.discriminant());
    if discr != std::cmp::Ordering::Equal {
      return discr;
    }
    match (self, other) {
      (String(a), String(b)) | (Symbol(a), Symbol(b)) => resolve_name(*a).cmp(&resolve_name(*b)),
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Property {
  pub key: PropKey,
  pub data: PropData,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Indexer {
  pub key_type: TypeId,
  pub value_type: TypeId,
  pub readonly: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ObjectType {
  pub shape: ShapeId,
}

#[derive(Default, Debug)]
pub(crate) struct ShapeInterner {
  pub items: Vec<Shape>,
  pub map: ahash::AHashMap<Shape, ShapeId>,
}

impl ShapeInterner {
  pub fn intern(&mut self, shape: Shape) -> ShapeId {
    if let Some(id) = self.map.get(&shape) {
      return *id;
    }
    let id = ShapeId(self.items.len() as u32);
    self.items.push(shape.clone());
    self.map.insert(shape, id);
    id
  }
}

#[derive(Default, Debug)]
pub(crate) struct ObjectInterner {
  pub items: Vec<ObjectType>,
  pub map: ahash::AHashMap<ObjectType, ObjectId>,
}

impl ObjectInterner {
  pub fn intern(&mut self, object: ObjectType) -> ObjectId {
    if let Some(id) = self.map.get(&object) {
      return *id;
    }
    let id = ObjectId(self.items.len() as u32);
    self.items.push(object.clone());
    self.map.insert(object, id);
    id
  }
}
