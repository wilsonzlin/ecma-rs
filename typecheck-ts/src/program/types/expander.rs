use super::*;

#[derive(Clone, Copy)]
pub(in super::super) struct ProgramTypeExpander<'a> {
  pub(in super::super) def_types: &'a HashMap<DefId, TypeId>,
  pub(in super::super) type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
  pub(in super::super) intrinsics: &'a HashMap<DefId, tti::IntrinsicKind>,
}

impl<'a> tti::TypeExpander for ProgramTypeExpander<'a> {
  fn expand(
    &self,
    store: &tti::TypeStore,
    def: DefId,
    args: &[TypeId],
  ) -> Option<tti::ExpandedType> {
    if let Some(kind) = self.intrinsics.get(&def).copied() {
      let operand = args
        .first()
        .copied()
        .unwrap_or_else(|| store.primitive_ids().unknown);
      let ty = store.intern_type(tti::TypeKind::Intrinsic { kind, ty: operand });
      return Some(tti::ExpandedType {
        params: Vec::new(),
        ty,
      });
    }
    let ty = *self.def_types.get(&def)?;
    let params = self.type_params.get(&def).cloned().unwrap_or_else(Vec::new);
    Some(tti::ExpandedType { params, ty })
  }
}
