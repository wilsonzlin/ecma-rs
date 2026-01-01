use derive_visitor::{DriveMut, VisitorMut};
use parse_js::ast::class_or_object::ClassStaticBlock;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;

type TopLevelNode = Node<TopLevel>;
type FuncNode = Node<Func>;
type StaticBlockNode = Node<ClassStaticBlock>;

#[derive(VisitorMut)]
#[visitor(TopLevelNode(enter), FuncNode(enter), StaticBlockNode(enter))]
struct BodyVisitor<'a> {
  apply: &'a mut dyn FnMut(Vec<Node<Stmt>>, &mut bool) -> Vec<Node<Stmt>>,
  changed: bool,
}

impl BodyVisitor<'_> {
  fn enter_top_level_node(&mut self, node: &mut TopLevelNode) {
    let body = std::mem::take(&mut node.stx.body);
    node.stx.body = (self.apply)(body, &mut self.changed);
  }

  fn enter_func_node(&mut self, node: &mut FuncNode) {
    let Some(body) = node.stx.body.as_mut() else {
      return;
    };
    let FuncBody::Block(stmts) = body else {
      return;
    };
    let owned = std::mem::take(stmts);
    *stmts = (self.apply)(owned, &mut self.changed);
  }

  fn enter_static_block_node(&mut self, node: &mut StaticBlockNode) {
    let body = std::mem::take(&mut node.stx.body);
    node.stx.body = (self.apply)(body, &mut self.changed);
  }
}

pub(super) fn apply_to_function_like_bodies<F>(top: &mut Node<TopLevel>, apply: F) -> bool
where
  F: FnMut(Vec<Node<Stmt>>, &mut bool) -> Vec<Node<Stmt>>,
{
  let mut apply = apply;
  let mut visitor = BodyVisitor {
    apply: &mut apply,
    changed: false,
  };
  top.drive_mut(&mut visitor);
  visitor.changed
}
