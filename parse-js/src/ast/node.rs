use std::any::{Any, TypeId};
use ahash::HashMap;
use derive_visitor::{Drive, DriveMut};
use std::fmt::{Debug, Formatter};
use std::fmt;
use serde::{Deserialize, Serialize, Serializer};
use crate::error::{SyntaxError, SyntaxErrorType};
use crate::loc::Loc;

#[derive(Default)]
pub struct NodeAssocData {
  // Make Node movable across threads (e.g. rayon) by bounding value to Send + Sync too.
  map: HashMap<TypeId, Box<dyn Any + Send + Sync>>,
}

impl NodeAssocData {
  pub fn get<T: Any>(&self) -> Option<&T> {
    let t = TypeId::of::<T>();
    self.map.get(&t).map(|v| v.downcast_ref().unwrap())
  }

  pub fn set<T: Any + Send + Sync>(&mut self, v: T) {
    let t = TypeId::of::<T>();
    self.map.insert(t, Box::from(v));
  }
}

#[derive(Drive, DriveMut)]
pub struct Node<S: Drive + DriveMut> {
  // A location is not a SourceRange; consider that after some transformations, it's possible to create entirely new nodes that don't exist at all in the source code. Also, sometimes we cannot be bothered to set a location, or can only provide an approximate/best-effort location.
  #[drive(skip)]
  pub loc: Loc,
  pub stx: Box<S>,
  #[drive(skip)]
  pub assoc: NodeAssocData,
}

impl<S: Drive + DriveMut> Node<S> {
  pub fn new(loc: Loc, stx: S) -> Node<S> {
    Node {
      loc,
      stx: Box::new(stx),
      assoc: NodeAssocData::default(),
    }
  }

  pub fn into_stx<T: From<S> +  Drive + DriveMut>(self) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(T::from(*self.stx)),
      assoc: self.assoc,
    }
  }

  /// Maps the syntax, keeping the location and associated data.
  pub fn map_stx<T: Drive + DriveMut, F: FnOnce(S) -> T>(self, f: F) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(f(*self.stx)),
      assoc: self.assoc,
    }
  }

  /// Maps the syntax, copying the location but not the associated data.
  pub fn derive_stx<T: Drive + DriveMut, F: FnOnce(&S) -> T>(&self, f: F) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(f(&self.stx)),
      assoc: NodeAssocData::default(),
    }
  }

  /// Wraps the node inside another node with the same loc, with syntax derived from the provided callback.
  pub fn wrap<T: Drive + DriveMut, F: FnOnce(Node<S>) -> T>(self, f: F) -> Node<T> {
    let loc = self.loc;
    let stx = f(self);
    Node::new(loc, stx)
  }

  /// Create an error at this node's location.
  pub fn error(&self, typ: SyntaxErrorType) -> SyntaxError {
    self.loc.error(typ, None)
  }
}

impl<S: Debug + Drive + DriveMut> Debug for Node<S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    self.stx.fmt(f)
  }
}

impl<S: Serialize + Drive + DriveMut> Serialize for Node<S> {
  fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
    self.stx.serialize(serializer)
  }
}


#[cfg(test)]
mod tests {
  use crate::ast::node::NodeAssocData;

  #[test]
  fn test_node_assoc_data() {
    struct MyType(u32);
    let mut assoc = NodeAssocData::default();
    assoc.set(MyType(32));
    let v = assoc.get::<MyType>().unwrap();
    assert_eq!(v.0, 32);
  }
}
