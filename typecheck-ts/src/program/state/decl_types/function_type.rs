use super::*;

impl ProgramState {
  pub(super) fn infer_cached_callable_return_type(
    &mut self,
    func: &FuncData,
    store: &Arc<tti::TypeStore>,
    callable_ty: TypeId,
  ) -> Result<Option<TypeId>, FatalError> {
    let Some(body) = func.body else {
      return Ok(None);
    };
    let is_async = self.body_is_async_function(body);
    let tti::TypeKind::Callable { overloads } = store.type_kind(callable_ty) else {
      return Ok(None);
    };
    if overloads.len() != 1 {
      return Ok(None);
    }
    let mut ret = if self.checking_bodies.contains(&body) {
      store.primitive_ids().unknown
    } else {
      let res = self.check_body(body)?;
      if res.return_types.is_empty() {
        store.primitive_ids().void
      } else {
        let mut members = Vec::new();
        for ty in res.return_types.iter() {
          let ty = store.canon(*ty);
          let widened = check::widen::widen_literal(store.as_ref(), ty);
          members.push(widened);
        }
        store.union(members)
      }
    };
    let prim = store.primitive_ids();
    if is_async && ret != prim.unknown {
      ret = self
        .promise_ref(store.as_ref(), ret)
        .unwrap_or(prim.unknown);
    }
    let sig_id = overloads[0];
    let mut sig = store.signature(sig_id);
    if sig.ret == ret {
      return Ok(None);
    }
    sig.ret = ret;
    let sig_id = store.intern_signature(sig);
    let callable_ty = store.canon(store.intern_type(tti::TypeKind::Callable {
      overloads: vec![sig_id],
    }));
    Ok(Some(callable_ty))
  }

  fn body_is_async_function(&self, body_id: BodyId) -> bool {
    let Some(meta) = self.body_map.get(&body_id) else {
      return false;
    };
    let Some(hir_body_id) = meta.hir else {
      return false;
    };
    let Some(lowered) = self.hir_lowered.get(&meta.file) else {
      return false;
    };
    let Some(body) = lowered.body(hir_body_id) else {
      return false;
    };
    body.function.as_ref().is_some_and(|f| f.async_)
  }

  fn resolve_promise_def(&self) -> Option<tti::DefId> {
    let mut best: Option<((u8, u8, u32, u32, u64), DefId)> = None;
    for (def, data) in self.def_data.iter() {
      if data.name != "Promise" {
        continue;
      }
      let pri = self.def_priority(*def, sem_ts::Namespace::TYPE);
      if pri == u8::MAX {
        continue;
      }
      let origin = self.file_registry.lookup_origin(data.file);
      let origin_rank: u8 = if self.current_file == Some(data.file) {
        0
      } else if matches!(origin, Some(FileOrigin::Source)) {
        1
      } else {
        2
      };
      let span = data.span;
      let key = (origin_rank, pri, span.start, span.end, def.0);
      best = match best {
        Some((best_key, best_def)) if best_key <= key => Some((best_key, best_def)),
        _ => Some((key, *def)),
      };
    }
    best.map(|(_, def)| tti::DefId(def.0))
  }

  fn promise_ref(&self, store: &tti::TypeStore, inner: TypeId) -> Option<TypeId> {
    let def = self.resolve_promise_def()?;
    Some(store.canon(store.intern_type(tti::TypeKind::Ref {
      def,
      args: vec![store.canon(inner)],
    })))
  }

  pub(super) fn function_type(&mut self, def: DefId, func: FuncData) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let store = Arc::clone(&self.store);
    let prim = store.primitive_ids();
    let param_types: Vec<TypeId> = func
      .params
      .iter()
      .map(|p| p.typ.unwrap_or(prim.any))
      .map(|ty| self.resolve_value_ref_type(ty))
      .collect::<Result<Vec<_>, _>>()?;
    let inferred_from_body = func.return_ann.is_none() && func.body.is_some();
    let mut ret = if let Some(ret) = func.return_ann {
      self.resolve_value_ref_type(ret)?
    } else if let Some(body) = func.body {
      self.check_cancelled()?;
      if self.checking_bodies.contains(&body) {
        prim.unknown
      } else {
        let res = self.check_body(body)?;
        if res.return_types.is_empty() {
          prim.void
        } else {
          let mut widened = Vec::new();
          for ty in res.return_types.iter() {
            let ty = store.canon(*ty);
            widened.push(check::widen::widen_literal(store.as_ref(), ty));
          }
          store.union(widened)
        }
      }
    } else {
      prim.unknown
    };

    if inferred_from_body
      && func
        .body
        .is_some_and(|body| self.body_is_async_function(body))
    {
      if ret != prim.unknown {
        ret = self
          .promise_ref(store.as_ref(), ret)
          .unwrap_or(prim.unknown);
      }
    }

    let params: Vec<tti::Param> = param_types
      .into_iter()
      .map(|ty| tti::Param {
        name: None,
        ty: store.canon(ty),
        optional: false,
        rest: false,
      })
      .collect();
    let sig = tti::Signature::new(params, ret);
    let sig_id = store.intern_signature(sig);
    let callable_ty = store.canon(store.intern_type(tti::TypeKind::Callable {
      overloads: vec![sig_id],
    }));
    self.interned_def_types.insert(def, callable_ty);
    Ok(callable_ty)
  }
}
