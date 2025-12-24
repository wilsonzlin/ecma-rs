use ahash::HashMap;
use ahash::HashSet;
use derive_visitor::DriveMut;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use std::str::FromStr;
use symbol::Scope;
use symbol::ScopeType;
use symbol::Symbol;
use symbol::SymbolGenerator;
use visitor::DeclVisitor;

pub mod symbol;
pub mod var_analysis;
pub mod visitor;

pub use var_analysis::VarAnalysis;

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

#[derive(Debug)]
pub struct BindJsResult {
  pub captured: HashSet<Symbol>,
  pub use_before_decl: HashMap<Symbol, Loc>,
}

pub fn bind_js(top_level_node: &mut Node<TopLevel>, top_level_mode: TopLevelMode) -> BindJsResult {
  compute_symbols(top_level_node, top_level_mode);
  let VarAnalysis {
    foreign,
    use_before_decl,
    ..
  } = VarAnalysis::analyze(top_level_node);

  BindJsResult {
    captured: foreign,
    use_before_decl,
  }
}
