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
id_newtype!(NameId);
id_newtype!(TypeParamId);
id_newtype!(SignatureId);
id_newtype!(DefId);
