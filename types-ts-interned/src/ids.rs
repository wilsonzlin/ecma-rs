use serde::Deserialize;
use serde::Serialize;

macro_rules! id_newtype {
  ($name:ident) => {
    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, Debug)]
    pub struct $name(pub u32);

    impl From<u32> for $name {
      fn from(value: u32) -> Self {
        Self(value)
      }
    }

    impl $name {
      pub fn index(self) -> usize {
        self.0 as usize
      }
    }
  };
}

id_newtype!(TypeId);
id_newtype!(ObjectId);
id_newtype!(ShapeId);
id_newtype!(TypeParamId);
id_newtype!(SignatureId);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, Debug)]
pub struct NameId(pub u64);

impl From<u64> for NameId {
  fn from(value: u64) -> Self {
    Self(value)
  }
}

// `DefId` is shared with `hir-js` to ensure a single canonical definition identity
// throughout the pipeline. It is re-exported here for convenience.
pub use hir_js::DefId;
