use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::token::TT;
#[cfg(feature = "diagnostics")]
use diagnostics::{FileId as DiagnosticFileId, Span as DiagnosticSpan, TextRange as DiagnosticTextRange};
use std::cmp::{max, min};
use std::ops::{Add, AddAssign};

/// A half-open byte range within a single file.
///
/// Offsets are **UTF-8 byte offsets** and are intended to line up with
/// `diagnostics::TextRange`/`Span` when paired with a file identifier.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TextRange {
  pub start: u32,
  pub end: u32,
}

impl TextRange {
  pub const fn new(start: u32, end: u32) -> Self {
    Self { start, end }
  }

  pub fn len(&self) -> u32 {
    self.end.saturating_sub(self.start)
  }

  pub fn contains(&self, offset: u32) -> bool {
    offset >= self.start && offset < self.end
  }

  pub fn is_empty(&self) -> bool {
    self.start >= self.end
  }

  pub fn from_loc_saturating(loc: Loc) -> (Self, Option<LocOverflow>) {
    let (start, start_overflow) = clamp_to_u32(loc.0);
    let (end, end_overflow) = clamp_to_u32(loc.1);
    let overflow = LocOverflow {
      start: start_overflow,
      end: end_overflow,
    };
    let overflow = overflow.into_option();
    (Self { start, end }, overflow)
  }

  /// Attempts to convert a `Loc` into a `TextRange` without truncating offsets.
  pub fn checked_from_loc(loc: Loc) -> Result<Self, LocOverflow> {
    let (range, overflow) = TextRange::from_loc_saturating(loc);
    match overflow {
      Some(overflow) => Err(overflow),
      None => Ok(range),
    }
  }

  #[cfg(feature = "diagnostics")]
  /// Convert this range into a `diagnostics` range for downstream consumers.
  pub fn to_diagnostics(self) -> DiagnosticTextRange {
    DiagnosticTextRange::new(self.start, self.end)
  }
}

impl From<Loc> for TextRange {
  /// Converts a `Loc` into a `TextRange`, clamping to `u32::MAX` on overflow.
  ///
  /// Use [`TextRange::checked_from_loc`] or [`Loc::as_range_with_overflow`] if
  /// you need to detect truncation.
  fn from(value: Loc) -> Self {
    TextRange::from_loc_saturating(value).0
  }
}

impl From<TextRange> for Loc {
  fn from(range: TextRange) -> Self {
    Loc(range.start as usize, range.end as usize)
  }
}

#[cfg(feature = "diagnostics")]
impl From<Loc> for DiagnosticTextRange {
  fn from(value: Loc) -> Self {
    value.to_diagnostics_range()
  }
}

/// Indicates which ends of a [`Loc`] could not fit into a `u32`.
///
/// When an endpoint overflows, the original offset is stored in the
/// corresponding field.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LocOverflow {
  pub start: Option<usize>,
  pub end: Option<usize>,
}

impl LocOverflow {
  pub fn start_overflowed(&self) -> bool {
    self.start.is_some()
  }

  pub fn end_overflowed(&self) -> bool {
    self.end.is_some()
  }

  pub fn any(&self) -> bool {
    self.start_overflowed() || self.end_overflowed()
  }

  fn into_option(self) -> Option<Self> {
    self.any().then_some(self)
  }
}

/// A location within the current source file expressed as UTF-8 byte offsets.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Loc(pub usize, pub usize);

impl Loc {
  /// Returns the starting offset as `u32`, clamping to `u32::MAX` if necessary.
  pub fn start_u32(&self) -> u32 {
    clamp_to_u32(self.0).0
  }

  /// Returns the ending offset as `u32`, clamping to `u32::MAX` if necessary.
  pub fn end_u32(&self) -> u32 {
    clamp_to_u32(self.1).0
  }

  /// Converts this `Loc` into a [`TextRange`], clamping to `u32` on overflow.
  pub fn as_range(&self) -> TextRange {
    (*self).into()
  }

  /// Converts this `Loc` into a [`TextRange`] while reporting whether any
  /// boundary overflowed `u32`.
  pub fn as_range_with_overflow(&self) -> (TextRange, Option<LocOverflow>) {
    TextRange::from_loc_saturating(*self)
  }

  /// Creates a best-effort location for synthetic nodes where only one side of
  /// the range is known.
  ///
  /// If both bounds are missing, an empty location at offset 0 is returned.
  pub fn best_effort(start: Option<Loc>, end: Option<Loc>) -> Loc {
    match (start, end) {
      (Some(mut start), Some(end)) => {
        start.extend(end);
        start
      }
      (Some(start), None) => start,
      (None, Some(end)) => end,
      (None, None) => Loc(0, 0),
    }
  }

  #[cfg(feature = "diagnostics")]
  /// Convert this location into a `diagnostics::TextRange`, clamping to `u32`.
  pub fn to_diagnostics_range(&self) -> DiagnosticTextRange {
    self.as_range().to_diagnostics()
  }

  #[cfg(feature = "diagnostics")]
  /// Convert this location into a diagnostics range along with an overflow note if applicable.
  pub fn to_diagnostics_range_with_note(&self) -> (DiagnosticTextRange, Option<String>) {
    let (range, overflow) = self.as_range_with_overflow();
    let note = overflow.map(|_| {
      format!(
        "byte offsets truncated to fit u32 (start={}, end={})",
        self.0, self.1
      )
    });
    (range.to_diagnostics(), note)
  }

  #[cfg(feature = "diagnostics")]
  /// Convert this location into a `diagnostics::Span` tied to the given file.
  pub fn to_diagnostics_span(&self, file: DiagnosticFileId) -> DiagnosticSpan {
    DiagnosticSpan {
      file,
      range: self.to_diagnostics_range(),
    }
  }

  #[cfg(feature = "diagnostics")]
  /// Convert this location into a diagnostics span with an optional overflow note.
  pub fn to_diagnostics_span_with_note(
    &self,
    file: DiagnosticFileId,
  ) -> (DiagnosticSpan, Option<String>) {
    let (range, note) = self.to_diagnostics_range_with_note();
    (
      DiagnosticSpan {
        file,
        range,
      },
      note,
    )
  }

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

fn clamp_to_u32(value: usize) -> (u32, Option<usize>) {
  if value > u32::MAX as usize {
    (u32::MAX, Some(value))
  } else {
    (value as u32, None)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn converts_loc_into_range_without_overflow() {
    let loc = Loc(4, 10);
    let (range, overflow) = loc.as_range_with_overflow();
    assert_eq!(range, TextRange::new(4, 10));
    assert!(overflow.is_none());
    assert_eq!(loc.start_u32(), 4);
    assert_eq!(loc.end_u32(), 10);
  }

  #[test]
  fn loc_to_range_clamps_on_overflow() {
    let loc = Loc(usize::MAX, usize::MAX - 1);
    let (range, overflow) = loc.as_range_with_overflow();
    assert_eq!(range.start, u32::MAX);
    assert_eq!(range.end, u32::MAX);
    let overflow = overflow.expect("expected overflow information");
    assert!(overflow.start_overflowed());
    assert!(overflow.end_overflowed());
  }

  #[test]
  fn checked_from_loc_detects_overflow() {
    let loc = Loc(u32::MAX as usize + 1, 0);
    let result = TextRange::checked_from_loc(loc);
    assert!(matches!(
      result,
      Err(LocOverflow {
        start: Some(_),
        end: None
      })
    ));
  }

  #[test]
  fn text_range_to_loc_is_lossless() {
    let range = TextRange::new(u32::MAX, u32::MAX);
    let loc: Loc = range.into();
    assert_eq!(loc.0, u32::MAX as usize);
    assert_eq!(loc.1, u32::MAX as usize);
  }

  #[test]
  fn best_effort_loc_prefers_known_bounds() {
    let start = Loc(1, 2);
    let end = Loc(5, 6);
    assert_eq!(Loc::best_effort(Some(start), Some(end)), Loc(1, 6));
    assert_eq!(Loc::best_effort(Some(start), None), start);
    assert_eq!(Loc::best_effort(None, Some(end)), end);
    assert_eq!(Loc::best_effort(None, None), Loc(0, 0));
  }

  #[cfg(feature = "diagnostics")]
  #[test]
  fn loc_to_diagnostics_span_preserves_offsets() {
    let loc = Loc(2, 4);
    let span = loc.to_diagnostics_span(DiagnosticFileId(7));
    assert_eq!(span.file, DiagnosticFileId(7));
    assert_eq!(span.range, DiagnosticTextRange::new(2, 4));
  }
}
