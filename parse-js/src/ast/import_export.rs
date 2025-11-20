use super::expr::pat::IdPat;
use super::node::Node;
use super::stmt::decl::PatDecl;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::Serialize;

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ExportName {
  #[drive(skip)]
  pub type_only: bool, // TypeScript: export { type Foo }
  #[drive(skip)]
  pub exportable: String,
  // This is always set, even when no explicit alias is provided. This is for simplicity for downstream tasks, as an implicit alias hides the implicit IdPat usage.
  pub alias: Node<IdPat>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum ExportNames {
  // `export * from "module"`
  // `export * as name from "module"`
  All(Option<Node<IdPat>>),
  // `export {a as default, b as c, d, "e" as f}`
  // `export {default, a as b, c} from "module"`
  // `default` is still a name, so we don't use an enum.
  Specific(Vec<Node<ExportName>>),
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ImportName {
  #[drive(skip)]
  pub type_only: bool, // TypeScript: import { type Foo }
  #[drive(skip)]
  pub importable: String,
  // This is always set, even when no explicit alias is provided. This is for simplicity for downstream tasks, as an implicit alias hides the implicit IdPat decl.
  // PatDecl always contains IdPat.
  pub alias: Node<PatDecl>,
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub enum ImportNames {
  // `import * as name`
  // PatDecl always contains IdPat.
  All(Node<PatDecl>),
  // `import {a as b, c, default as e}`
  // `default` is still a name, so we don't use an enum.
  Specific(Vec<Node<ImportName>>),
}
