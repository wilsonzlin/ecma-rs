use ahash::{HashMap, HashSet};
use croaring::Bitmap;
use derive_visitor::Visitor;
use parse_js::ast::{expr::{pat::IdPat, IdExpr}, func::Func, node::Node, stmt::{decl::PatDecl, BlockStmt, CatchBlock, ForBody}};
use symbol_js::symbol::{Scope, Symbol};


// Given some scope (likely function), we have the task of assigning a name to each variable declared in it.
// We must not name a variable in such a way that we inadvertently shadow a variable in some ancestor scope that the current or any descendant scope uses.
// Only foreign and unknown variables can be used across scopes, so we only need to consider these.


type IdExprNode = Node<IdExpr>;
type PatDeclNode = Node<PatDecl>;
type IdPatNode = Node<IdPat>;

#[derive(Visitor)]
#[visitor(
  IdExprNode(enter),
)]
pub(crate) struct UsageVisitor {
  is_foreign: HashSet<Symbol>,
}

#[derive(Default)]
struct ScopeUsages {
  foreign: HashSet<Symbol>,
  unknown: HashSet<String>,
}

impl UsageVisitor {
  pub fn enter_id_expr_node(&mut self, node: &Node<IdExpr>) {
    let name = &node.stx.name;
    let scope = node.assoc.get::<Scope>().unwrap();
    let Some(sym) = scope.find_symbol(name.clone()) else {
      // Unknown.
      for ancestor in scope.self_and_ancestors() {
        ancestor.data_mut().get_or_insert_assoc::<ScopeUsages>().unknown.insert(name.clone());
      };
      return;
    };
    if !self.is_foreign.contains(&sym) {
      return;
    };
    for ancestor in scope.self_and_ancestors() {
    if ancestor.data().get_symbol(name).is_some() {
        break;
      };
      ancestor.data_mut().get_or_insert_assoc::<ScopeUsages>().foreign.insert(sym);
    };
  }
}

#[derive(Visitor)]
#[visitor(
  PatDeclNode,
  IdPatNode(enter),
)]
pub(crate) struct NamingVisitor {
  is_foreign: HashSet<Symbol>,
  in_pat_decl_stack: Vec<bool>,
}

struct ScopeFreeNames {
  free_name_ids: Bitmap,
}

impl ScopeFreeNames {
  pub fn take_next_free_name_id(&mut self) -> u32 {
    let id = self.free_name_ids.minimum().unwrap();
    self.free_name_ids.remove(id);
    id
  }
}

impl Default for ScopeFreeNames {
  fn default() -> Self {
    Self {
      free_name_ids: Bitmap::from_range(..),
    }
  }
}

impl NamingVisitor {
  pub fn enter_pat_decl_node(&mut self, _node: &Node<PatDecl>) {
    self.in_pat_decl_stack.push(true);
  }

  pub fn exit_pat_decl_node(&mut self, _node: &Node<PatDecl>) {
    self.in_pat_decl_stack.pop();
  }

  pub fn enter_id_pat_node(&mut self, node: &Node<IdPat>) {
    if !self.in_pat_decl_stack.last().cloned().unwrap_or_default() {
      return;
    }
    let name = &node.stx.name;
    let scope = node.assoc.get::<Scope>().unwrap();
    let sym = scope.data().get_symbol(name).unwrap();
    if !self.is_foreign.contains(&sym) {
      return;
    };
    let name_id = scope.data_mut().get_or_insert_assoc::<ScopeFreeNames>().take_next_free_name_id();
    // TODO Optimization: skip subtree of a scope if it doesn't use the variable.
    for d in scope.descendants() {
      if d.data().get_assoc::<ScopeUsages>().is_some_and(|u| u.foreign.contains(&sym)) {
        // This descendant scope uses the variable, so it cannot name one of its declared variables the same.
        d.data_mut().get_or_insert_assoc::<ScopeFreeNames>().free_name_ids.remove(name_id);
      };
    };
    // TODO Generate name given name_id and unknown usages (disallowed names) in current scope.
  }
}
