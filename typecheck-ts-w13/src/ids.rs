#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BodyId(pub usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PatId(pub usize);

impl BodyId {
  pub fn index(self) -> usize {
    self.0
  }
}

impl ExprId {
  pub fn index(self) -> usize {
    self.0
  }
}

impl PatId {
  pub fn index(self) -> usize {
    self.0
  }
}
