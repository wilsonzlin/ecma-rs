use parse_js::ast::node::Node;
use parse_js::visit::VisitorMut;
use symbol::Scope;
use symbol::ScopeType;
use symbol::SymbolGenerator;
use visitor::DeclVisitor;

pub mod symbol;
pub mod visitor;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TopLevelMode {
  Global,
  Module,
}

pub fn compute_symbols(top_level_node: &mut Node, top_level_mode: TopLevelMode) -> Scope {
  let top_level_scope = Scope::new(SymbolGenerator::new(), None, match top_level_mode {
    TopLevelMode::Global => ScopeType::Global,
    TopLevelMode::Module => ScopeType::Module,
  });
  let mut visitor = DeclVisitor::new(top_level_scope.clone());
  visitor.visit(top_level_node);
  top_level_scope
}
