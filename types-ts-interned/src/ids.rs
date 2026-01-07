macro_rules! id_newtype {
  ($name:ident, $inner:ty) => {
    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
    #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    pub struct $name(pub $inner);

    impl From<$inner> for $name {
      fn from(value: $inner) -> Self {
        Self(value)
      }
    }
  };
}

id_newtype!(TypeId, u128);
id_newtype!(ObjectId, u128);
id_newtype!(ShapeId, u128);
id_newtype!(TypeParamId, u32);
id_newtype!(SignatureId, u128);
id_newtype!(NameId, u64);

// `DefId` is shared with `hir-js` to ensure a single canonical definition identity
// throughout the pipeline. It is re-exported here for convenience.
pub use hir_js::DefId;
