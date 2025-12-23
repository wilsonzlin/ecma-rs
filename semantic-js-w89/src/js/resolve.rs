use super::semantics::JsSemantics;
use super::semantics::ScopeId;
use super::semantics::SymbolId;
use crate::assoc::declared_symbol;
use crate::assoc::scope_id;
use crate::assoc::ResolvedSymbol;
use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stx::TopLevel;

#[derive(Debug, Default)]
pub struct JsResolution {
  pub resolved: usize,
  pub unresolved: usize,
}

pub fn resolve(top_level: &mut Node<TopLevel>, sem: &JsSemantics) -> JsResolution {
  let mut visitor = ResolveVisitor {
    sem,
    resolved: 0,
    unresolved: 0,
  };
  top_level.drive_mut(&mut visitor);
  JsResolution {
    resolved: visitor.resolved,
    unresolved: visitor.unresolved,
  }
}

#[derive(VisitorMut)]
#[visitor(IdExprNode(enter), IdPatNode(enter))]
struct ResolveVisitor<'a> {
  sem: &'a JsSemantics,
  resolved: usize,
  unresolved: usize,
}

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;

impl<'a> ResolveVisitor<'a> {
  fn resolve_in_scope(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
    let mut current = Some(scope);
    while let Some(scope_id) = current {
      let scope_data = self.sem.scope(scope_id);
      if let Some(sym) = scope_data.symbol(name) {
        return Some(sym);
      }
      current = scope_data.parent;
    }
    None
  }

  fn mark(&mut self, assoc: &mut NodeAssocData, symbol: Option<SymbolId>) {
    assoc.set(ResolvedSymbol(symbol));
    if symbol.is_some() {
      self.resolved += 1;
    } else {
      self.unresolved += 1;
    }
  }

  fn resolve_use(&mut self, assoc: &mut NodeAssocData, name: &str) {
    if let Some(scope) = scope_id(assoc) {
      let symbol = self.resolve_in_scope(scope, name);
      self.mark(assoc, symbol);
    } else {
      self.mark(assoc, None);
    }
  }
}

impl ResolveVisitor<'_> {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    self.resolve_use(&mut node.assoc, &node.stx.name);
  }

  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    if let Some(declared) = declared_symbol(&node.assoc) {
      self.mark(&mut node.assoc, Some(declared));
    } else {
      self.resolve_use(&mut node.assoc, &node.stx.name);
    }
  }
}
