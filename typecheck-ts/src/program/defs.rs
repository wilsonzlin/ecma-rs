use crate::api::{BodyId, ExprId, FileId, PatId, TextRange};
use crate::semantic_js;
use parse_js::ast::stmt::decl::VarDeclMode;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use types_ts_interned::TypeId;

#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct DefData {
  pub name: String,
  pub file: FileId,
  pub span: TextRange,
  pub symbol: semantic_js::SymbolId,
  pub export: bool,
  pub kind: DefKind,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub enum DefKind {
  Function(FuncData),
  Var(VarData),
  VarDeclarator(VarDeclaratorData),
  Class(ClassData),
  Enum(EnumData),
  Namespace(NamespaceData),
  Module(ModuleData),
  Import(ImportData),
  ImportAlias(ImportAliasData),
  Interface(InterfaceData),
  TypeAlias(TypeAliasData),
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct FuncData {
  pub params: Vec<ParamData>,
  pub return_ann: Option<TypeId>,
  pub body: Option<BodyId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ParamData {
  pub name: String,
  pub typ: Option<TypeId>,
  pub symbol: semantic_js::SymbolId,
  pub pat: Option<PatId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct VarData {
  pub typ: Option<TypeId>,
  pub init: Option<ExprId>,
  pub body: BodyId,
  #[cfg_attr(
    feature = "serde",
    serde(skip_serializing, skip_deserializing, default = "default_var_mode")
  )]
  pub mode: VarDeclMode,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct VarDeclaratorData {
  pub body: Option<BodyId>,
}

#[cfg(feature = "serde")]
fn default_var_mode() -> VarDeclMode {
  VarDeclMode::Var
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ImportData {
  pub target: ImportTarget,
  pub original: String,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ImportAliasData {
  pub path: Vec<String>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub enum ImportTarget {
  File(FileId),
  Unresolved { specifier: String },
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct InterfaceData {
  pub typ: TypeId,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct TypeAliasData {
  pub typ: TypeId,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ClassData {
  pub body: Option<BodyId>,
  pub instance_type: Option<TypeId>,
  pub static_type: Option<TypeId>,
  pub declare: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct EnumData {
  pub body: Option<BodyId>,
  pub is_const: bool,
  pub value_type: Option<TypeId>,
  pub type_type: Option<TypeId>,
  pub declare: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct NamespaceData {
  pub body: Option<BodyId>,
  pub value_type: Option<TypeId>,
  pub type_type: Option<TypeId>,
  pub declare: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ModuleData {
  pub body: Option<BodyId>,
  pub value_type: Option<TypeId>,
  pub type_type: Option<TypeId>,
  pub declare: bool,
}
