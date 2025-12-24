use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::token::TT;
#[cfg(feature = "diagnostics")]
use diagnostics::Span;
#[cfg(feature = "diagnostics")]
use diagnostics::TextRange;
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

  #[cfg(feature = "diagnostics")]
  /// Convert this `Loc` into a diagnostics `TextRange`, saturating to `u32` and
  /// returning a note if truncation occurred.
  pub fn to_diagnostics_range(self) -> (TextRange, Option<String>) {
    let (start, start_overflow) = saturating_to_u32(self.0);
    let (end, end_overflow) = saturating_to_u32(self.1);
    let note = if start_overflow || end_overflow {
      Some(format!(
        "byte offsets truncated to fit u32 (start={}, end={})",
        self.0, self.1
      ))
    } else {
      None
    };
    (TextRange::new(start, end), note)
  }

  #[cfg(feature = "diagnostics")]
  /// Convert this `Loc` into a diagnostics span for the given file.
  pub fn to_diagnostics_span(self, file: diagnostics::FileId) -> (Span, Option<String>) {
    let (range, note) = self.to_diagnostics_range();
    (Span::new(file, range), note)
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

#[cfg(feature = "diagnostics")]
impl From<Loc> for TextRange {
  /// Converts a `Loc` into a diagnostics text range by saturating to `u32`. Any
  /// truncation can be observed via [`Loc::to_diagnostics_range`].
  fn from(value: Loc) -> Self {
    value.to_diagnostics_range().0
  }
}

#[cfg(feature = "diagnostics")]
fn saturating_to_u32(value: usize) -> (u32, bool) {
  if value > u32::MAX as usize {
    (u32::MAX, true)
  } else {
    (value as u32, false)
  }
}
