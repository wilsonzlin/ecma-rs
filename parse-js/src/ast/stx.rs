use super::node::Node;
use super::stmt::Stmt;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::Serialize;

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TopLevel {
  pub body: Vec<Node<Stmt>>,
}
