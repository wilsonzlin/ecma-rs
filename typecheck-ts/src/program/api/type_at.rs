use super::*;

impl Program {
  /// Innermost expression covering an offset within a file.
  pub fn expr_at(&self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    match self.expr_at_fallible(file, offset) {
      Ok(expr) => expr,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn expr_at_fallible(
    &self,
    file: FileId,
    offset: u32,
  ) -> Result<Option<(BodyId, ExprId)>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.expr_at(file, offset)))
  }

  /// Type of the innermost expression covering an offset within a file.
  pub fn type_at(&self, file: FileId, offset: u32) -> Option<TypeId> {
    match self.type_at_fallible(file, offset) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn type_at_fallible(&self, file: FileId, offset: u32) -> Result<Option<TypeId>, FatalError> {
    self.with_interned_state(|state| {
      const TYPE_AT_TRIVIA_LOOKAROUND: usize = 32;

      let store = Arc::clone(&state.store);
      let mut offset = offset;
      let mut expr_at = state.expr_at(file, offset);
      let mut pat_at = state.pat_at(file, offset);

      if expr_at.is_none() && pat_at.is_none() {
        if let Ok(text) = state.load_text(file, &self.host) {
          let bytes = text.as_bytes();
          let start = (offset as usize).min(bytes.len());

          let mut found = None;
          for step in 1..=TYPE_AT_TRIVIA_LOOKAROUND {
            if start < step {
              break;
            }
            let cand = start - step;
            let Ok(cand_u32) = cand.try_into() else {
              break;
            };
            if state.expr_at(file, cand_u32).is_some() || state.pat_at(file, cand_u32).is_some() {
              found = Some(cand_u32);
              break;
            }
          }

          if found.is_none() {
            for step in 1..=TYPE_AT_TRIVIA_LOOKAROUND {
              let cand = start + step;
              if cand >= bytes.len() {
                break;
              }
              let Ok(cand_u32) = cand.try_into() else {
                break;
              };
              if state.expr_at(file, cand_u32).is_some() || state.pat_at(file, cand_u32).is_some() {
                found = Some(cand_u32);
                break;
              }
            }
          }

          if let Some(adj) = found {
            offset = adj;
            expr_at = state.expr_at(file, offset);
            pat_at = state.pat_at(file, offset);
          }
        }
      }

      let (body, expr) = match expr_at {
        Some(res) => res,
        None => {
          let Some((body, pat)) = pat_at else {
            return Ok(None);
          };
          let result = state.check_body(body)?;
          let unknown = state.interned_unknown();
          return Ok(Some(result.pat_type(pat).unwrap_or(unknown)));
        }
      };
      let result = state.check_body(body)?;
      let unknown = state.interned_unknown();
      let (expr, mut ty) = match result.expr_at(offset) {
        Some((expr_id, ty)) => (expr_id, ty),
        None => (expr, result.expr_type(expr).unwrap_or(unknown)),
      };
      let mut member_fallback: Option<(bool, tti::TypeId, String)> = None;
      let mut binding_def: Option<DefId> = None;
      let mut binding_ty: Option<TypeId> = None;
      let mut contextual_ty: Option<TypeId> = None;
      if let Some(meta) = state.body_map.get(&body) {
        if let Some(hir_id) = meta.hir {
          if let Some(lowered) = state.hir_lowered.get(&meta.file) {
            if let Some(hir_body) = lowered.body(hir_id) {
              if let Some(expr_data) = hir_body.exprs.get(expr.0 as usize) {
                match &expr_data.kind {
                  HirExprKind::Ident(name_id) => {
                    if let Some(name) = lowered.names.resolve(*name_id) {
                      if let Some(file_state) = state.files.get(&meta.file) {
                        if let Some(binding) = file_state.bindings.get(name) {
                          binding_def = binding.def;
                          binding_ty = binding.type_id;
                        }
                      }
                    }
                  }
                  HirExprKind::Member(mem) => {
                    let key = match &mem.property {
                      hir_js::ObjectKey::Ident(id) => {
                        lowered.names.resolve(*id).map(|s| s.to_string())
                      }
                      hir_js::ObjectKey::String(s) => Some(s.clone()),
                      hir_js::ObjectKey::Number(n) => Some(n.clone()),
                      hir_js::ObjectKey::Computed(_) => None,
                    };
                    if let Some(key) = key {
                      let base_ty = result.expr_type(mem.object).unwrap_or(unknown);
                      member_fallback = Some((mem.optional, base_ty, key));
                    }
                  }
                  _ => {}
                }
                if contextual_ty.is_none() {
                  for (_idx, candidate) in hir_body.exprs.iter().enumerate() {
                    if let HirExprKind::Call(call) = &candidate.kind {
                      if let Some(arg_idx) = call.args.iter().position(|arg| arg.expr.0 == expr.0) {
                        if let Some(callee_ty) = result.expr_type(call.callee) {
                          let sigs = callable_signatures(store.as_ref(), callee_ty);
                          if let Some(sig_id) = sigs.first() {
                            let sig = store.signature(*sig_id);
                            if let Some(param) = sig.params.get(arg_idx) {
                              contextual_ty = Some(param.ty);
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if let Some(ctx) = contextual_ty {
        ty = ctx;
      }
      let is_unknown = !store.contains_type_id(ty)
        || matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
      let should_resolve_binding = is_unknown
        || (store.contains_type_id(ty)
          && matches!(
            store.type_kind(store.canon(ty)),
            tti::TypeKind::Ref { def, args }
              if args.is_empty() && binding_def.map(|bd| bd.0 == def.0).unwrap_or(false)
          ));
      if should_resolve_binding {
        if let Some(def) = binding_def {
          match state.type_of_def(def) {
            Ok(def_ty) => {
              ty = store.canon(def_ty);
            }
            Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
            Err(_) => {}
          }
        }
        let still_unknown = !store.contains_type_id(ty)
          || matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
        if still_unknown {
          if let Some(binding_ty) = binding_ty {
            ty = binding_ty;
          }
        }
      }
      let member_fallback_allowed = !store.contains_type_id(ty)
        || matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
      if member_fallback_allowed {
        if let Some((optional, base_ty, key)) = member_fallback {
          let caches = state.checker_caches.for_body();
          let expander = RefExpander::new(
            Arc::clone(&store),
            &state.interned_def_types,
            &state.interned_type_params,
            &state.interned_type_param_decls,
            &state.interned_intrinsics,
            &state.interned_class_instances,
            caches.eval.clone(),
          );
          let mut prop_ty =
            lookup_interned_property_type(store.as_ref(), Some(&expander), base_ty, &key);
          if prop_ty.is_none() {
            if let tti::TypeKind::Ref { def, .. } = store.type_kind(store.canon(base_ty)) {
              if let Some(mapped) = state.interned_def_types.get(&DefId(def.0)).copied() {
                prop_ty = lookup_interned_property_type(store.as_ref(), None, mapped, &key);
              }
            }
          }
          if let Some(prop_ty) = prop_ty {
            ty = if optional {
              store.union(vec![prop_ty, store.primitive_ids().undefined])
            } else {
              prop_ty
            };
          }
        }
      }
      if std::env::var("DEBUG_TYPE_AT").is_ok() {
        if let Some(span) = result.expr_span(expr) {
          eprintln!(
            "type_at debug: body {:?} expr {:?} span {:?}",
            body, expr, span
          );
        } else {
          eprintln!("type_at debug: body {:?} expr {:?} (no span)", body, expr);
        }
        if let Some(meta) = state.body_map.get(&body) {
          eprintln!("  meta kind {:?}", meta.kind);
          if let Some(hir_id) = meta.hir {
            if let Some(lowered) = state.hir_lowered.get(&meta.file) {
              if let Some(hir_body) = lowered.body(hir_id) {
                if let Some(expr_data) = hir_body.exprs.get(expr.0 as usize) {
                  eprintln!("  hir expr kind {:?}", expr_data.kind);
                }
              }
            }
          }
        }
        eprintln!("  parent {:?}", state.body_parents.get(&body));
        if let Some(raw_ty) = result.expr_type(expr) {
          if store.contains_type_id(raw_ty) {
            eprintln!("  raw type {:?}", store.type_kind(raw_ty));
          } else {
            eprintln!("  raw type {:?}", raw_ty);
          }
        }
        if let Some(parent) = state.body_parents.get(&body).copied() {
          match state.check_body(parent) {
            Ok(parent_res) => {
              eprintln!("  parent pat types {:?}", parent_res.pat_types());
              if let Some(first) = parent_res.pat_types().first() {
                if store.contains_type_id(*first) {
                  eprintln!("  parent pat kind {:?}", store.type_kind(*first));
                }
              }
            }
            Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
            Err(_) => {}
          }
        }
        if let Some(owner) = state.owner_of_body(body) {
          if let Some(def) = state.def_data.get(&owner) {
            eprintln!("  owner {:?}", def.name);
          }
        }
        if let Some(parent) = state.body_parents.get(&body).copied() {
          if let Some(owner) = state.owner_of_body(parent) {
            if let Some(def) = state.def_data.get(&owner) {
              eprintln!("  parent owner {:?}", def.name);
            }
          }
        }
      }
      let is_number_literal = state
        .store
        .contains_type_id(ty)
        && matches!(store.type_kind(store.canon(ty)), tti::TypeKind::NumberLiteral(_));
      if is_number_literal {
        let is_literal = state
          .body_map
          .get(&body)
          .and_then(|meta| meta.hir)
          .and_then(|hir_id| {
            state
              .hir_lowered
              .get(&file)
              .and_then(|lowered| lowered.body(hir_id))
              .and_then(|hir_body| {
                hir_body
                  .exprs
                  .get(expr.0 as usize)
                  .map(|expr_data| matches!(expr_data.kind, HirExprKind::Literal(_)))
              })
          })
          .unwrap_or(false);
        if is_literal {
          if let Some(meta) = state.body_map.get(&body) {
            if let Some(hir_id) = meta.hir {
              if let Some(lowered) = state.hir_lowered.get(&meta.file) {
                if let Some(hir_body) = lowered.body(hir_id) {
                  let mut best: Option<(u32, TypeId)> = None;
                  for (idx, expr_data) in hir_body.exprs.iter().enumerate() {
                    let span = expr_data.span;
                    if !(span.start <= offset && offset < span.end) {
                      continue;
                    }
                    if let HirExprKind::Binary { op, .. } = &expr_data.kind {
                      let numeric = matches!(
                        op,
                        HirBinaryOp::Add
                          | HirBinaryOp::Subtract
                          | HirBinaryOp::Multiply
                          | HirBinaryOp::Divide
                          | HirBinaryOp::Exponent
                          | HirBinaryOp::Remainder
                          | HirBinaryOp::BitAnd
                          | HirBinaryOp::BitOr
                          | HirBinaryOp::BitXor
                          | HirBinaryOp::ShiftLeft
                          | HirBinaryOp::ShiftRight
                          | HirBinaryOp::ShiftRightUnsigned
                      );
                      if !numeric {
                        continue;
                      }
                      let len = span.len();
                      let bin_ty = result.expr_type(ExprId(idx as u32)).unwrap_or(ty);
                      let is_number = store.contains_type_id(bin_ty)
                        && matches!(store.type_kind(store.canon(bin_ty)), tti::TypeKind::Number);
                      if is_number {
                        let replace = best.map(|(l, _)| len < l).unwrap_or(true);
                        if replace {
                          best = Some((len, bin_ty));
                        }
                      }
                    }
                  }
                  if let Some((_, bin_ty)) = best {
                    ty = bin_ty;
                  }
                }
              }
            }
          }
        }
      }
      let ty = if store.contains_type_id(ty) {
        store.canon(ty)
      } else {
        unknown
      };
      Ok(Some(ty))
    })
  }
}
