use crate::ids::DefId;
use crate::ids::ExprId;
use diagnostics::TextRange;

#[derive(Debug, Default, Clone, PartialEq)]
pub struct SpanMap {
  exprs: Vec<(TextRange, ExprId)>,
  defs: Vec<(TextRange, DefId)>,
}

impl SpanMap {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add_expr(&mut self, range: TextRange, id: ExprId) {
    self.exprs.push((range, id));
  }

  pub fn add_def(&mut self, range: TextRange, id: DefId) {
    self.defs.push((range, id));
  }

  pub fn finalize(&mut self) {
    self.exprs.sort_by(|(a_range, a_id), (b_range, b_id)| {
      (a_range.start, a_range.end, a_id).cmp(&(b_range.start, b_range.end, b_id))
    });
    self.defs.sort_by(|(a_range, a_id), (b_range, b_id)| {
      (a_range.start, a_range.end, a_id).cmp(&(b_range.start, b_range.end, b_id))
    });
  }

  pub fn expr_at_offset(&self, offset: u32) -> Option<ExprId> {
    self
      .exprs
      .iter()
      .filter(|(range, _)| range.contains(offset))
      .min_by(|(a_range, a_id), (b_range, b_id)| {
        let a_len = a_range.len();
        let b_len = b_range.len();
        (a_len, a_range.start, *a_id).cmp(&(b_len, b_range.start, *b_id))
      })
      .map(|(_, id)| *id)
  }

  pub fn def_at_offset(&self, offset: u32) -> Option<DefId> {
    self
      .defs
      .iter()
      .filter(|(range, _)| range.contains(offset))
      .min_by(|(a_range, a_id), (b_range, b_id)| {
        let a_len = a_range.len();
        let b_len = b_range.len();
        (a_len, a_range.start, *a_id).cmp(&(b_len, b_range.start, *b_id))
      })
      .map(|(_, id)| *id)
  }
}

#[cfg(test)]
mod tests {
  use super::SpanMap;
  use crate::ids::DefId;
  use crate::ids::ExprId;
  use diagnostics::TextRange;

  #[test]
  fn prefers_inner_expr() {
    let mut map = SpanMap::new();
    map.add_expr(TextRange::new(0, 10), ExprId(0));
    map.add_expr(TextRange::new(2, 4), ExprId(1));
    map.finalize();
    assert_eq!(map.expr_at_offset(3), Some(ExprId(1)));
  }

  #[test]
  fn def_lookup_is_stable() {
    let mut map = SpanMap::new();
    map.add_def(TextRange::new(0, 5), DefId(0));
    map.add_def(TextRange::new(0, 4), DefId(1));
    map.finalize();
    assert_eq!(map.def_at_offset(1), Some(DefId(1)));
  }
}
