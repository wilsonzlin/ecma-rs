//! Association helpers for data attached to `parse-js` AST nodes.
//!
//! This module is split by language mode to avoid collisions between JS-only
//! and TS-only identifiers. Downstream users should pick the helpers that
//! match the binder they ran (`assoc::js` for [`crate::js`], `assoc::ts` for
//! [`crate::ts`]).

pub mod js;
pub mod ts;

/// Stable key for side tables built from AST node spans.
///
/// Side-table based binders avoid mutating `NodeAssocData` by indexing attached
/// data by source byte ranges instead. `SpanKey` preserves deterministic ordering
/// via its `Ord` implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpanKey {
  pub start: u32,
  pub end: u32,
}

impl SpanKey {
  pub const fn new(start: u32, end: u32) -> Self {
    Self { start, end }
  }
}

impl From<parse_js::loc::Loc> for SpanKey {
  fn from(loc: parse_js::loc::Loc) -> Self {
    Self {
      start: loc.start_u32(),
      end: loc.end_u32(),
    }
  }
}

impl From<parse_js::loc::TextRange> for SpanKey {
  fn from(range: parse_js::loc::TextRange) -> Self {
    Self {
      start: range.start,
      end: range.end,
    }
  }
}

impl From<diagnostics::TextRange> for SpanKey {
  fn from(range: diagnostics::TextRange) -> Self {
    Self {
      start: range.start,
      end: range.end,
    }
  }
}
