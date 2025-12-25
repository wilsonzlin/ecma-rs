use crate::ids::NameId;
use crate::ids::TypeId;
use crate::ids::TypeParamId;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Param {
  pub name: Option<NameId>,
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Signature {
  pub params: Vec<Param>,
  pub ret: TypeId,
  pub type_params: Vec<TypeParamId>,
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
