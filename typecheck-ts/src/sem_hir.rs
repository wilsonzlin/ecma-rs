use hir_js::LowerResult;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use semantic_js::ts as sem_ts;

pub(crate) fn sem_hir_from_lower(ast: &Node<TopLevel>, lowered: &LowerResult) -> sem_ts::HirFile {
  sem_ts::from_hir_js::lower_to_ts_hir(ast, lowered)
}
