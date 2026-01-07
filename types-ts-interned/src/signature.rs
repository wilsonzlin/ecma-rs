use crate::ids::NameId;
use crate::ids::TypeId;
use crate::ids::TypeParamId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeParamVariance {
  In,
  Out,
  InOut,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeParamDecl {
  pub id: TypeParamId,
  pub constraint: Option<TypeId>,
  pub default: Option<TypeId>,
  pub variance: Option<TypeParamVariance>,
  pub const_: bool,
}

impl TypeParamDecl {
  pub fn new(id: TypeParamId) -> Self {
    Self {
      id,
      constraint: None,
      default: None,
      variance: None,
      const_: false,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Param {
  pub name: Option<NameId>,
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Signature {
  pub params: Vec<Param>,
  pub ret: TypeId,
  pub type_params: Vec<TypeParamDecl>,
  pub this_param: Option<TypeId>,
}

impl Signature {
  pub fn new(params: Vec<Param>, ret: TypeId) -> Self {
    Self {
      params,
      ret,
      type_params: Vec::new(),
      this_param: None,
    }
  }
}
