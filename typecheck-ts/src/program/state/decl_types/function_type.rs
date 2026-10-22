use super::*;
use crate::program::check::decls::{HirDeclLowerer, LocalDefIndex, ValueFunctionSignature};

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
    let is_generator = self.body_is_generator_function(body);
    let tti::TypeKind::Callable { overloads } = store.type_kind(callable_ty) else {
      return Ok(None);
    };
    if overloads.len() != 1 {
      return Ok(None);
    }
    let checking = self
      .checking_bodies
      .lock()
      .unwrap_or_else(|err| err.into_inner())
      .contains(&body);
    let ret = if checking {
      store.primitive_ids().unknown
    } else {
      let res = self.check_body(body)?;
      let return_union = if res.return_types.is_empty() {
        store.primitive_ids().void
      } else {
        let mut members = Vec::new();
        for ty in res.return_types.iter() {
          let ty = store.canon(*ty);
          let widened = check::widen::widen_literal(store.as_ref(), ty);
          members.push(widened);
        }
        store.union(members)
      };
      if is_generator {
        // Generators return `Generator<Y, R, N>` (async: `AsyncGenerator`),
        // built from the body's yield union — not the raw `return` union or
        // `void` (`function* gen() { yield 1; }` is
        // `() => Generator<number, void, unknown>`, never `() => void`).
        // Falls back to the raw type when the global generator interfaces
        // cannot be resolved (e.g. no lib).
        let prim = store.primitive_ids();
        let yield_union = if res.yield_types.is_empty() {
          prim.never
        } else {
          let mut members = Vec::new();
          for ty in res.yield_types.iter() {
            let ty = store.canon(*ty);
            let widened = check::widen::widen_literal(store.as_ref(), ty);
            members.push(widened);
          }
          store.union(members)
        };
        let name = if is_async {
          "AsyncGenerator"
        } else {
          "Generator"
        };
        self
          .named_global_type(
            store.as_ref(),
            name,
            &[yield_union, return_union, prim.unknown],
          )
          .unwrap_or(return_union)
      } else {
        let prim = store.primitive_ids();
        if is_async && return_union != prim.unknown {
          self
            .promise_ref(store.as_ref(), return_union)
            .unwrap_or(prim.unknown)
        } else {
          return_union
        }
      }
    };
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

  fn body_is_generator_function(&self, body_id: BodyId) -> bool {
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
    body.function.as_ref().is_some_and(|f| f.generator)
  }

  /// Whether this function has an explicit return type annotation (binder
  /// `FuncData` or HIR `FunctionData` when the binder left annotations unset).
  pub(in super::super) fn function_has_return_annotation(
    &self,
    def: DefId,
    func: &FuncData,
  ) -> bool {
    if func.return_ann.is_some() {
      return true;
    }
    let Some(def_data) = self.def_data.get(&def) else {
      return false;
    };
    let Some(lowered) = self.hir_lowered.get(&def_data.file) else {
      return false;
    };
    let Some(hir_def) = lowered.def(def) else {
      return false;
    };
    let Some(body_id) = hir_def.body else {
      return false;
    };
    let Some(body) = lowered.body(body_id) else {
      return false;
    };
    body
      .function
      .as_ref()
      .is_some_and(|f| f.return_type.is_some())
  }

  fn lower_hir_value_function_signature(&mut self, def: DefId) -> Option<ValueFunctionSignature> {
    let file = self.def_data.get(&def)?.file;
    let lowered = self.hir_lowered.get(&file)?.clone();
    let hir_def = lowered.def(def)?;
    let body_id = hir_def.body?;
    let body = lowered.body(body_id)?;
    let func = body.function.as_ref()?.clone();

    let store = Arc::clone(&self.store);
    let mut diagnostics = Vec::new();
    let local_defs = LocalDefIndex::from_lowered(&lowered);
    let mut binding_defs = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        if let Some(bdef) = binding.def {
          binding_defs.insert(name.clone(), bdef);
        }
      }
    }
    let prev_file = self.current_file;
    self.current_file = Some(file);
    let program_resolver = self.build_type_resolver(&binding_defs);
    let resolve_name = |path: &[String]| -> Option<DefId> {
      program_resolver
        .as_ref()
        .and_then(|r| r.resolve_type_name(path))
    };
    let mut lowerer = HirDeclLowerer::new(
      store,
      &lowered.types,
      self.semantics.as_deref(),
      HashMap::new(),
      file,
      self.file_key_for_id(file),
      local_defs,
      &mut diagnostics,
      None,
      None,
      None,
      None,
      Some(&self.module_namespace_defs),
      Some(&self.value_defs),
    )
    .with_type_name_resolver(&resolve_name);
    // Needed for `typeof import("…").x` on arrow/value signatures (resolves
    // module + qualifier via ProgramTypeResolver, not type-name-only lookup).
    if let Some(resolver) = program_resolver.clone() {
      lowerer = lowerer.with_type_resolver(resolver);
    }
    // `body` was borrowed from `lowered`; re-resolve after building the lowerer.
    let body = lowered.body(body_id).expect("body present");
    let enclosing = crate::class_typing::enclosing_class_type_params(&lowered, hir_def.id);
    let sig = match enclosing.as_ref() {
      Some((class_id, params)) => lowerer.lower_value_function_signature_with_class_params(
        def,
        &func,
        body,
        Some((*class_id, params.as_slice())),
        &lowered.names,
      ),
      None => lowerer.lower_value_function_signature(def, &func, body, &lowered.names),
    };
    self.current_file = prev_file;
    if self.semantics.is_some() {
      self.diagnostics.extend(diagnostics);
    }
    Some(sig)
  }

  fn resolve_promise_def(&self) -> Option<tti::DefId> {
    self.resolve_global_type_def("Promise")
  }

  /// Highest-priority global type with `name` (e.g. `Generator`,
  /// `AsyncGenerator`), using the same origin/priority ordering as
  /// [`Self::resolve_promise_def`].
  fn resolve_global_type_def(&self, name: &str) -> Option<tti::DefId> {
    let mut best: Option<((u8, u8, u32, u32, u64), DefId)> = None;
    for (def, data) in self.def_data.iter() {
      if data.name != name {
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

  /// Global named type applied to arguments (`Generator<Y, R, N>`,
  /// `AsyncGenerator<Y, R, N>`) when the global interface can be resolved.
  fn named_global_type(
    &self,
    store: &tti::TypeStore,
    name: &str,
    args: &[TypeId],
  ) -> Option<TypeId> {
    let def = self.resolve_global_type_def(name)?;
    Some(store.canon(store.intern_type(tti::TypeKind::Ref {
      def,
      args: args.to_vec(),
    })))
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

    // Prefer HIR `FunctionData` param/return annotations when present. Binder
    // leaves `FuncData` annotations unset once HIR is available.
    let hir_sig = self.lower_hir_value_function_signature(def);
    if let Some(ref sig) = hir_sig {
      // Cache lowered annotations back onto FuncData for nested-body binding seeds.
      if let Some(data) = self.def_data.get_mut(&def) {
        if let DefKind::Function(existing) = &mut data.kind {
          let mut binder_idx = 0usize;
          for param in existing.params.iter_mut() {
            if param.name == "this" {
              continue;
            }
            if param.typ.is_none() {
              if let Some(Some(ty)) = sig.param_types_for_binder.get(binder_idx).copied() {
                param.typ = Some(ty);
              }
            }
            binder_idx += 1;
          }
          if existing.return_ann.is_none() {
            existing.return_ann = sig.return_ann;
          }
        }
      }
    }

    let (param_types, optional_rest, this_param, type_params, hir_return) =
      if let Some(sig) = hir_sig {
        let optional_rest: Vec<(bool, bool)> =
          sig.params.iter().map(|p| (p.optional, p.rest)).collect();
        let param_types: Vec<TypeId> = sig
          .params
          .iter()
          .map(|p| self.resolve_value_ref_type(p.ty))
          .collect::<Result<Vec<_>, _>>()?;
        (
          param_types,
          optional_rest,
          sig.this_param,
          sig.type_params,
          sig.return_ann,
        )
      } else {
        let this_param = func
          .params
          .first()
          .filter(|p| p.name == "this")
          .and_then(|p| p.typ);
        let param_types: Vec<TypeId> = func
          .params
          .iter()
          .filter(|p| p.name != "this")
          .map(|p| p.typ.unwrap_or(prim.any))
          .map(|ty| self.resolve_value_ref_type(ty))
          .collect::<Result<Vec<_>, _>>()?;
        let optional_rest = param_types.iter().map(|_| (false, false)).collect();
        (
          param_types,
          optional_rest,
          this_param,
          Vec::new(),
          func.return_ann,
        )
      };

    let has_return_ann = hir_return.is_some() || func.return_ann.is_some();
    let inferred_from_body = !has_return_ann && func.body.is_some();
    let mut ret = if let Some(ret) = hir_return.or(func.return_ann) {
      self.resolve_value_ref_type(ret)?
    } else if let Some(body) = func.body {
      self.check_cancelled()?;
      let checking = self
        .checking_bodies
        .lock()
        .unwrap_or_else(|err| err.into_inner())
        .contains(&body);
      if checking {
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
      .zip(optional_rest)
      .map(|(ty, (optional, rest))| tti::Param {
        name: None,
        ty: store.canon(ty),
        optional,
        rest,
      })
      .collect();
    let this_param = match this_param {
      Some(ty) => Some(self.resolve_value_ref_type(ty)?),
      None => None,
    };
    let sig = tti::Signature {
      params,
      ret,
      type_params,
      this_param,
    };
    let sig_id = store.intern_signature(sig);
    let callable_ty = store.canon(store.intern_type(tti::TypeKind::Callable {
      overloads: vec![sig_id],
    }));
    self.interned_def_types.insert(def, callable_ty);
    Ok(callable_ty)
  }
}
