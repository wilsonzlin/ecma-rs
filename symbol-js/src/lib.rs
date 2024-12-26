use derive_visitor::DriveMut;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
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

pub fn compute_symbols(top_level_node: &mut Node<TopLevel>, top_level_mode: TopLevelMode) -> Scope {
  let top_level_scope = Scope::new(SymbolGenerator::new(), None, match top_level_mode {
    TopLevelMode::Global => ScopeType::Global,
    TopLevelMode::Module => ScopeType::Module,
  });
  let mut visitor = DeclVisitor::new(top_level_scope.clone());
  top_level_node.drive_mut(&mut visitor);
  top_level_scope
}
