use super::node::Node;
use super::stmt::Stmt;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Drive, DriveMut)]
pub struct TopLevel {
  pub body: Vec<Node<Stmt>>,
}
