use super::*;

impl ProgramState {
  pub(super) fn export_type_for_def(&mut self, def: DefId) -> Result<Option<TypeId>, FatalError> {
    self.rebuild_callable_overloads();
    if let Some(store) = self.interned_store.clone() {
      let mut cache = HashMap::new();
      if let Some(merged) = self.callable_overload_type_for_def(def, &store, &mut cache) {
        return Ok(Some(merged));
      }
      if let Some(defs) = self.callable_overload_defs(def) {
        if defs.len() > 1 {
          if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache) {
            return Ok(Some(merged));
          }
        }
      }
      let needs_recompute = match self.def_types.get(&def).copied() {
        Some(existing) => {
          let in_bounds = self.type_store.contains_id(existing);
          !(in_bounds && !matches!(self.type_store.kind(existing), TypeKind::Unknown))
        }
        None => true,
      };
      if needs_recompute {
        self.type_of_def(def)?;
      }
      if let Some(ty) = self.interned_def_types.get(&def).copied() {
        if !matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown) {
          return Ok(Some(ty));
        }
      }
      let Some(store_ty) = self.def_types.get(&def).copied() else {
        return Ok(None);
      };
      let interned = convert_type_for_display(store_ty, self, &store, &mut cache);
      let interned = store.canon(interned);
      self.interned_def_types.insert(def, interned);
      Ok(Some(interned))
    } else {
      let needs_recompute = match self.def_types.get(&def).copied() {
        Some(existing) => {
          let in_bounds = self.type_store.contains_id(existing);
          !(in_bounds && !matches!(self.type_store.kind(existing), TypeKind::Unknown))
        }
        None => true,
      };
      if needs_recompute {
        self.type_of_def(def)?;
      }
      Ok(self.def_types.get(&def).copied())
    }
  }

  pub(super) fn import_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref().cloned() else {
      return self.builtin.unknown;
    };
    use tti::TypeKind as InternedKind;
    match store.type_kind(ty) {
      InternedKind::Any => self.builtin.any,
      InternedKind::Unknown => self.builtin.unknown,
      InternedKind::Never => self.builtin.never,
      InternedKind::Void => self.builtin.void,
      InternedKind::Null => self.builtin.null,
      InternedKind::Undefined => self.builtin.undefined,
      InternedKind::Boolean => self.builtin.boolean,
      InternedKind::Number => self.builtin.number,
      InternedKind::String => self.builtin.string,
      InternedKind::BooleanLiteral(value) => self.type_store.literal_boolean(value),
      InternedKind::NumberLiteral(value) => self.type_store.literal_number(value.to_string()),
      InternedKind::StringLiteral(name) => {
        let name = store.name(name);
        self.type_store.literal_string(name)
      }
      InternedKind::Tuple(elems) => {
        let readonly = elems.iter().all(|elem| elem.readonly);
        let members: Vec<_> = elems
          .iter()
          .map(|elem| self.import_interned_type(elem.ty))
          .collect();
        self.type_store.tuple(members, readonly)
      }
      InternedKind::Array { ty, .. } => {
        let inner = self.import_interned_type(ty);
        self.type_store.array(inner)
      }
      InternedKind::Union(types) => {
        let mapped: Vec<_> = types
          .iter()
          .map(|t| self.import_interned_type(*t))
          .collect();
        self.type_store.union(mapped, &self.builtin)
      }
      InternedKind::Object(obj) => {
        let obj = store.object(obj);
        let shape = store.shape(obj.shape);
        let mut legacy = ObjectType::empty();
        for prop in shape.properties {
          let name = match prop.key {
            tti::PropKey::String(id) | tti::PropKey::Symbol(id) => Some(store.name(id)),
            tti::PropKey::Number(num) => Some(num.to_string()),
          };
          if let Some(name) = name {
            legacy.props.insert(
              name,
              ObjectProperty {
                typ: self.import_interned_type(prop.data.ty),
                optional: prop.data.optional,
                readonly: prop.data.readonly,
              },
            );
          }
        }
        for indexer in shape.indexers {
          let value = self.import_interned_type(indexer.value_type);
          match store.type_kind(indexer.key_type) {
            InternedKind::String => legacy.string_index = Some(value),
            InternedKind::Number => legacy.number_index = Some(value),
            _ => {}
          }
        }
        self.type_store.object(legacy)
      }
      InternedKind::Predicate {
        parameter,
        asserted,
        asserts,
      } => {
        let param = match parameter {
          Some(tti::PredicateParam::This) => "this".to_string(),
          _ => String::new(),
        };
        let asserted = asserted.map(|ty| self.import_interned_type(ty));
        self.type_store.predicate(param, asserted, asserts)
      }
      InternedKind::Callable { overloads } => {
        let mut fns = Vec::new();
        for sig_id in overloads {
          let sig = store.signature(sig_id);
          let params = sig
            .params
            .iter()
            .map(|param| self.import_interned_type(param.ty))
            .collect();
          let ret = self.import_interned_type(sig.ret);
          fns.push(self.type_store.function(params, ret));
        }
        if fns.is_empty() {
          self.builtin.unknown
        } else {
          self.type_store.union(fns, &self.builtin)
        }
      }
      _ => self.builtin.unknown,
    }
  }

  pub(super) fn ensure_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    if store.contains_type_id(ty) {
      return store.canon(ty);
    }
    if let Some(mapped) = self.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        self.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return store.canon(mapped);
    }
    let mut cache = HashMap::new();
    let interned = convert_type_for_display(ty, self, store, &mut cache);
    store.canon(interned)
  }

  pub(super) fn is_unknown_type_id(&self, ty: TypeId) -> bool {
    if self.type_store.contains_id(ty) {
      return matches!(self.type_store.kind(ty), TypeKind::Unknown);
    }
    if let Some(store) = self.interned_store.as_ref() {
      if store.contains_type_id(ty) {
        return matches!(store.type_kind(store.canon(ty)), tti::TypeKind::Unknown);
      }
    }
    true
  }

  pub(super) fn prefer_named_refs(&self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    self.prefer_named_refs_in_store(store, ty)
  }

  pub(super) fn prefer_named_refs_in_store(&self, store: &Arc<tti::TypeStore>, ty: TypeId) -> TypeId {
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

  pub(super) fn prefer_named_class_refs_in_store(&self, store: &Arc<tti::TypeStore>, ty: TypeId) -> TypeId {
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

  pub(super) fn resolve_value_ref_type(&mut self, ty: TypeId) -> Result<TypeId, FatalError> {
    let Some(store) = self.interned_store.clone() else {
      return Ok(ty);
    };
    if std::env::var("DEBUG_OVERLOAD").is_ok() {
      if store.contains_type_id(ty) {
        eprintln!(
          "DEBUG resolve_value_ref_type input kind {:?}",
          store.type_kind(store.canon(ty))
        );
      } else {
        eprintln!("DEBUG resolve_value_ref_type input not in store");
      }
    }
    if !store.contains_type_id(ty) {
      return Ok(ty);
    }
    let canonical = store.canon(ty);
    if let tti::TypeKind::Ref { def, args } = store.type_kind(canonical) {
      if args.is_empty() {
        let def_id = DefId(def.0);
        if self.type_stack.contains(&def_id) {
          return Ok(canonical);
        }
        let should_resolve = self
          .def_data
          .get(&def_id)
          .map(|data| {
            matches!(
              data.kind,
              DefKind::Function(_)
                | DefKind::Var(_)
                | DefKind::Class(_)
                | DefKind::Enum(_)
                | DefKind::Namespace(_)
                | DefKind::Module(_)
                | DefKind::Import(_)
            )
          })
          .unwrap_or(false);
        if should_resolve {
          if std::env::var("DEBUG_OVERLOAD").is_ok() {
            if let Some(data) = self.def_data.get(&def_id) {
              eprintln!(
                "DEBUG resolve_value_ref_type ref to {} {:?}",
                data.name, data.kind
              );
            }
          }
          let resolved = self.type_of_def(def_id)?;
          let resolved = self.ensure_interned_type(resolved);
          if std::env::var("DEBUG_OVERLOAD").is_ok() {
            eprintln!(
              "DEBUG resolve_value_ref_type resolved kind {:?}",
              store.type_kind(resolved)
            );
          }
          if !matches!(store.type_kind(resolved), tti::TypeKind::Unknown) {
            return Ok(store.canon(resolved));
          }
        }
      }
    }
    Ok(canonical)
  }

  pub(super) fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      _ => ty,
    }
  }

  pub(super) fn widen_union_literals(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      TypeKind::Union(types) => {
        let members: Vec<_> = types
          .into_iter()
          .map(|t| self.widen_union_literals(t))
          .collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  pub(super) fn widen_array_elements(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(*inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  pub(super) fn widen_object_literal(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::Object(mut obj) => {
        let mut changed = false;
        for prop in obj.props.values_mut() {
          if prop.readonly {
            continue;
          }
          let widened = self.widen_union_literals(prop.typ);
          if widened != prop.typ {
            prop.typ = widened;
            changed = true;
          }
        }
        if let Some(value) = obj.string_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.string_index = Some(widened);
            changed = true;
          }
        }
        if let Some(value) = obj.number_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.number_index = Some(widened);
            changed = true;
          }
        }
        if changed {
          self.type_store.object(obj)
        } else {
          ty
        }
      }
      _ => ty,
    }
  }

  pub(super) fn init_is_satisfies(&self, body: BodyId, expr: ExprId) -> bool {
    let meta = match self.body_map.get(&body) {
      Some(meta) => meta,
      None => return false,
    };
    let hir_id = match meta.hir {
      Some(id) => id,
      None => return false,
    };
    let lowered = match self.hir_lowered.get(&meta.file) {
      Some(lowered) => lowered,
      None => return false,
    };
    let hir_body = match lowered.body(hir_id) {
      Some(body) => body,
      None => return false,
    };
    hir_body
      .exprs
      .get(expr.0 as usize)
      .map(|e| matches!(e.kind, HirExprKind::Satisfies { .. }))
      .unwrap_or(false)
  }

  pub(super) fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    if let Some(def_data) = self.def_data.get(&def) {
      if let DefKind::Var(var) = &def_data.kind {
        if var.body != MISSING_BODY {
          if let Some(expr) = var.init {
            let decl_kind = match var.mode {
              VarDeclMode::Var => HirVarDeclKind::Var,
              VarDeclMode::Let => HirVarDeclKind::Let,
              VarDeclMode::Const => HirVarDeclKind::Const,
              VarDeclMode::Using => HirVarDeclKind::Using,
              VarDeclMode::AwaitUsing => HirVarDeclKind::AwaitUsing,
            };
            let pat = if self.snapshot_loaded {
              self
                .body_results
                .get(&var.body)
                .and_then(|result| {
                  result
                    .pat_spans
                    .iter()
                    .position(|span| *span == def_data.span)
                })
                .map(|idx| PatId(idx as u32))
            } else {
              self.body_map.get(&var.body).and_then(|meta| {
                let hir_id = meta.hir?;
                self
                  .hir_lowered
                  .get(&meta.file)
                  .and_then(|lowered| lowered.body(hir_id))
                  .and_then(|body| {
                    body.pats.iter().enumerate().find_map(|(idx, pat)| {
                      (pat.span == def_data.span).then_some(PatId(idx as u32))
                    })
                  })
              })
            };
            return Some(VarInit {
              body: var.body,
              expr,
              decl_kind,
              pat,
              span: Some(def_data.span),
            });
          }
        }
      }
    }

    if self.snapshot_loaded {
      return None;
    }

    if let Some(init) = crate::db::var_initializer(&self.typecheck_db, def) {
      if std::env::var("DEBUG_OVERLOAD").is_ok() {
        if let Some(data) = self.def_data.get(&def) {
          eprintln!("DEBUG var initializer for {} -> {:?}", data.name, init);
        }
      }
      return Some(init);
    }

    let def_data = self.def_data.get(&def)?;
    let lowered = self.hir_lowered.get(&def_data.file)?;
    let hir_def = lowered.def(def)?;
    let def_name = lowered.names.resolve(hir_def.path.name);
    if !matches!(
      hir_def.path.kind,
      HirDefKind::Var | HirDefKind::VarDeclarator
    ) && def_name != Some("default")
    {
      return None;
    }
    let def_name = def_name.or_else(|| Some(def_data.name.as_str()));
    var_initializer_in_file(lowered, def, hir_def.span, def_name)
  }

}
