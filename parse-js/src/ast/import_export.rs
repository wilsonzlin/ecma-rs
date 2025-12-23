use super::expr::pat::IdPat;
use super::node::Node;
use super::stmt::decl::PatDecl;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Clone)]
pub enum ModuleExportImportName {
  Ident(String),
  Str(String),
}

impl ModuleExportImportName {
  pub fn as_str(&self) -> &str {
    match self {
      ModuleExportImportName::Ident(name) | ModuleExportImportName::Str(name) => name,
    }
  }
}

#[derive(Debug, Drive, DriveMut, Serialize)]
pub struct ExportName {
  #[drive(skip)]
  pub type_only: bool, // TypeScript: export { type Foo }
  #[drive(skip)]
  pub exportable: ModuleExportImportName,
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
  pub importable: ModuleExportImportName,
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

#[cfg(test)]
mod tests {
  use super::ModuleExportImportName;
  use serde_json::json;

  #[test]
  fn module_export_import_name_serializes_with_tag() {
    let ident = ModuleExportImportName::Ident("\\u0061".into());
    let serialized_ident = serde_json::to_value(&ident).unwrap();
    assert_eq!(serialized_ident, json!({"Ident": "\\u0061"}));
    let ident_roundtrip: ModuleExportImportName = serde_json::from_value(serialized_ident).unwrap();
    assert_eq!(ident_roundtrip, ident);

    let string_name = ModuleExportImportName::Str("\\u0061".into());
    let serialized_string = serde_json::to_value(&string_name).unwrap();
    assert_eq!(serialized_string, json!({"Str": "\\u0061"}));
    let string_roundtrip: ModuleExportImportName =
      serde_json::from_value(serialized_string).unwrap();
    assert_eq!(string_roundtrip, string_name);
  }
}
