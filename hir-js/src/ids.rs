use diagnostics::FileId;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BodyId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PatId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StmtId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DefKind {
  Module,
  Namespace,
  Class,
  Function,
  Method,
  Constructor,
  Field,
  Var,
  Param,
  TypeAlias,
  Interface,
  Enum,
  EnumMember,
  ImportBinding,
  ExportAlias,
  TypeParam,
  Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefPath {
  pub module: FileId,
  pub kind: DefKind,
  pub name: NameId,
  pub disambiguator: u32,
}

impl DefPath {
  pub fn new(module: FileId, kind: DefKind, name: NameId, disambiguator: u32) -> Self {
    Self {
      module,
      kind,
      name,
      disambiguator,
    }
  }
}
