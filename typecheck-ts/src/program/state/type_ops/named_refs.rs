use super::*;

impl ProgramState {
  pub(in super::super) fn prefer_named_refs(&self, ty: TypeId) -> TypeId {
    self.prefer_named_refs_in_store(&self.store, ty)
  }

  pub(in super::super) fn prefer_named_refs_in_store(
    &self,
    store: &Arc<tti::TypeStore>,
    ty: TypeId,
  ) -> TypeId {
    let canonical = store.canon(ty);
    let kind = store.type_kind(canonical);
    let primitive_like = matches!(
      kind,
      tti::TypeKind::Any
        | tti::TypeKind::Unknown
        | tti::TypeKind::Never
        | tti::TypeKind::Void
        | tti::TypeKind::Null
        | tti::TypeKind::Undefined
        | tti::TypeKind::Boolean
        | tti::TypeKind::Number
        | tti::TypeKind::String
        | tti::TypeKind::BigInt
        | tti::TypeKind::Symbol
        | tti::TypeKind::UniqueSymbol
        | tti::TypeKind::Callable { .. }
        | tti::TypeKind::BooleanLiteral(_)
        | tti::TypeKind::NumberLiteral(_)
        | tti::TypeKind::StringLiteral(_)
        | tti::TypeKind::BigIntLiteral(_)
        | tti::TypeKind::This
        | tti::TypeKind::TypeParam(_)
    );
    if !primitive_like {
      if let Some(def) = self.interned_named_def_types.get(&canonical).copied() {
        let mut args = self
          .interned_type_params
          .get(&def)
          .cloned()
          .unwrap_or_default();
        args.sort_by_key(|param| param.0);
        let args: Vec<_> = args
          .into_iter()
          .map(|param| store.intern_type(tti::TypeKind::TypeParam(param)))
          .collect();
        return store.canon(store.intern_type(tti::TypeKind::Ref { def, args }));
      }
    }
    match kind {
      tti::TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.union(mapped);
      }
      tti::TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.intersection(mapped);
      }
      tti::TypeKind::Array { ty, readonly } => {
        let mapped = self.prefer_named_refs_in_store(store, ty);
        if mapped != ty {
          return store.intern_type(tti::TypeKind::Array {
            ty: mapped,
            readonly,
          });
        }
      }
      tti::TypeKind::Tuple(elems) => {
        let mut changed = false;
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| {
            let mapped = self.prefer_named_refs_in_store(store, elem.ty);
            changed |= mapped != elem.ty;
            tti::TupleElem {
              ty: mapped,
              optional: elem.optional,
              rest: elem.rest,
              readonly: elem.readonly,
            }
          })
          .collect();
        if changed {
          return store.intern_type(tti::TypeKind::Tuple(mapped));
        }
      }
      _ => {}
    }
    canonical
  }

  pub(in super::super) fn prefer_named_class_refs_in_store(
    &self,
    store: &Arc<tti::TypeStore>,
    ty: TypeId,
  ) -> TypeId {
    let canonical = store.canon(ty);
    let kind = store.type_kind(canonical);
    let primitive_like = matches!(
      kind,
      tti::TypeKind::Any
        | tti::TypeKind::Unknown
        | tti::TypeKind::Never
        | tti::TypeKind::Void
        | tti::TypeKind::Null
        | tti::TypeKind::Undefined
        | tti::TypeKind::Boolean
        | tti::TypeKind::Number
        | tti::TypeKind::String
        | tti::TypeKind::BigInt
        | tti::TypeKind::Symbol
        | tti::TypeKind::UniqueSymbol
        | tti::TypeKind::Callable { .. }
        | tti::TypeKind::BooleanLiteral(_)
        | tti::TypeKind::NumberLiteral(_)
        | tti::TypeKind::StringLiteral(_)
        | tti::TypeKind::BigIntLiteral(_)
        | tti::TypeKind::This
        | tti::TypeKind::TypeParam(_)
    );
    if !primitive_like {
      if let Some(def) = self.interned_named_def_types.get(&canonical).copied() {
        if self
          .def_data
          .get(&def)
          .is_some_and(|data| matches!(data.kind, DefKind::Class(_)))
        {
          let mut args = self
            .interned_type_params
            .get(&def)
            .cloned()
            .unwrap_or_default();
          args.sort_by_key(|param| param.0);
          let args: Vec<_> = args
            .into_iter()
            .map(|param| store.intern_type(tti::TypeKind::TypeParam(param)))
            .collect();
          return store.canon(store.intern_type(tti::TypeKind::Ref { def, args }));
        }
      }
    }
    match kind {
      tti::TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_class_refs_in_store(store, member))
          .collect();
        return store.union(mapped);
      }
      tti::TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_class_refs_in_store(store, member))
          .collect();
        return store.intersection(mapped);
      }
      tti::TypeKind::Array { ty, readonly } => {
        let mapped = self.prefer_named_class_refs_in_store(store, ty);
        if mapped != ty {
          return store.intern_type(tti::TypeKind::Array {
            ty: mapped,
            readonly,
          });
        }
      }
      tti::TypeKind::Tuple(elems) => {
        let mut changed = false;
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| {
            let mapped = self.prefer_named_class_refs_in_store(store, elem.ty);
            changed |= mapped != elem.ty;
            tti::TupleElem {
              ty: mapped,
              optional: elem.optional,
              rest: elem.rest,
              readonly: elem.readonly,
            }
          })
          .collect();
        if changed {
          return store.intern_type(tti::TypeKind::Tuple(mapped));
        }
      }
      _ => {}
    }
    canonical
  }
}
