use crate::fixtures::Fixture;
use crate::fixtures::ModuleGraphFixture;
use derive_visitor::Drive;
use derive_visitor::Visitor;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stx::TopLevel;
use parse_js::error::SyntaxResult;
use parse_js::parse;
use symbol_js::compute_symbols;
use symbol_js::symbol::Scope;
use symbol_js::TopLevelMode;

#[derive(Clone, Copy, Debug)]
pub struct HirSummary {
  pub node_count: usize,
  pub max_depth: usize,
}

#[derive(Default, Visitor)]
#[visitor(NodeAssocData(enter, exit))]
struct HirLoweringVisitor {
  depth: usize,
  nodes: usize,
  max_depth: usize,
}

impl HirLoweringVisitor {
  fn enter_node_assoc_data(&mut self, _node: &NodeAssocData) {
    self.depth += 1;
    self.nodes += 1;
    self.max_depth = self.max_depth.max(self.depth);
  }

  fn exit_node_assoc_data(&mut self, _node: &NodeAssocData) {
    self.depth -= 1;
  }
}

pub fn parse_only(fixture: &Fixture) -> SyntaxResult<Node<TopLevel>> {
  parse(fixture.source)
}

pub fn lower_to_hir(top_level: &Node<TopLevel>) -> HirSummary {
  let mut visitor = HirLoweringVisitor::default();
  top_level.drive(&mut visitor);
  HirSummary {
    node_count: visitor.nodes,
    max_depth: visitor.max_depth,
  }
}

pub fn bind_single_file(source: &str, mode: TopLevelMode) -> usize {
  let mut parsed = parse(source).expect("fixture should parse before binding");
  let scope = compute_symbols(&mut parsed, mode);
  count_symbols(&scope)
}

pub fn bind_module_graph(graph: &ModuleGraphFixture) -> usize {
  graph
    .files
    .iter()
    .map(|fixture| bind_single_file(fixture.source, TopLevelMode::Module))
    .sum()
}

fn count_symbols(scope: &Scope) -> usize {
  let data = scope.data();
  let mut total = data.symbol_count();
  for child in data.children() {
    total += count_symbols(child);
  }
  total
}
