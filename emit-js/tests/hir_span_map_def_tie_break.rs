use diagnostics::TextRange;
use hir_js::{span_map::SpanMap, DefId, DefKind};

#[test]
fn def_at_offset_prefers_var_defs_over_shadowing_params() {
  let mut map = SpanMap::new();
  map.add_def(TextRange::new(0, 1), DefKind::Param, DefId(0));
  map.add_def(TextRange::new(0, 1), DefKind::Var, DefId(1));
  map.finalize();

  assert_eq!(map.def_at_offset(0), Some(DefId(1)));
}
