use std::{any::Any, fmt::Debug};

use derive_more::derive::From;
use derive_visitor::{Drive, DriveMut};
use serde::Serialize;

use super::{expr::Expr, node::Node, stmt::Stmt};

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct TopLevel {
  pub body: Vec<Node<Stmt>>,
}
