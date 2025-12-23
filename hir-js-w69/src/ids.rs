use std::convert::TryInto;

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BodyId(pub u32);

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StmtId(pub u32);

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PatId(pub u32);

macro_rules! impl_id {
  ($name:ident) => {
    impl $name {
      pub(crate) fn from_index(idx: usize) -> Self {
        let raw: u32 = idx
          .try_into()
          .unwrap_or_else(|_| panic!("too many {} nodes", stringify!($name)));
        Self(raw)
      }

      pub fn index(self) -> usize {
        self.0 as usize
      }

      pub fn raw(self) -> u32 {
        self.0
      }
    }
  };
}

impl_id!(BodyId);
impl_id!(ExprId);
impl_id!(StmtId);
impl_id!(PatId);
