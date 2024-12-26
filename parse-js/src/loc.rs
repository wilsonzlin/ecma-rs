use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::token::TT;
use std::cmp::max;
use std::cmp::min;
use std::ops::Add;
use std::ops::AddAssign;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Loc(pub usize, pub usize);

impl Loc {
  pub fn error(self, typ: SyntaxErrorType, actual_token: Option<TT>) -> SyntaxError {
    SyntaxError::new(typ, self, actual_token)
  }

  pub fn is_empty(&self) -> bool {
    self.0 >= self.1
  }

  pub fn len(&self) -> usize {
    self.1 - self.0
  }

  pub fn extend(&mut self, other: Loc) {
    self.0 = min(self.0, other.0);
    self.1 = max(self.1, other.1);
  }

  pub fn add_option(self, rhs: Option<Loc>) -> Loc {
    let mut new = self;
    if let Some(rhs) = rhs {
      new.extend(rhs);
    };
    new
  }
}

impl Add for Loc {
  type Output = Loc;

  fn add(self, rhs: Self) -> Self::Output {
    let mut new = self;
    new.extend(rhs);
    new
  }
}

impl AddAssign for Loc {
  fn add_assign(&mut self, rhs: Self) {
    self.extend(rhs);
  }
}
