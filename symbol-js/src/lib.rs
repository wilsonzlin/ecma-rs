use derive_visitor::DriveMut;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use std::str::FromStr;
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

impl FromStr for TopLevelMode {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "global" | "Global" => Ok(TopLevelMode::Global),
      "module" | "Module" => Ok(TopLevelMode::Module),
      _ => Err(()),
    }
  }
}

pub fn compute_symbols(top_level_node: &mut Node<TopLevel>, top_level_mode: TopLevelMode) -> Scope {
  let top_level_scope = Scope::new(
    SymbolGenerator::new(),
    None,
    match top_level_mode {
      TopLevelMode::Global => ScopeType::Global,
      TopLevelMode::Module => ScopeType::Module,
    },
  );
  let mut visitor = DeclVisitor::new(top_level_scope.clone());
  top_level_node.drive_mut(&mut visitor);
  top_level_scope
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn compute_symbols_handles_for_in_of_decl_lhs() {
    let source = "for (let x of y) {}\nfor (var z in o) {}\n";
    let mut ast = parse_js::parse(source).expect("parse failed");

    let _scope = compute_symbols(&mut ast, TopLevelMode::Module);
  }
}
