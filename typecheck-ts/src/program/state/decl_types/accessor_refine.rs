use super::*;

impl ProgramState {
  /// Fill class getter/setter property types from accessor function inference.
  ///
  /// HIR `ClassMemberSig` only carries explicit return/param annotations, so
  /// unannotated `get g() { return this.a; }` was lowered as `unknown` and
  /// `let x = this.g` spuriously TC3000 under `--noImplicitAny`. Accessors are
  /// `DefKind::Function`; `type_of_def` infers return/params from the body.
  pub(in super::super) fn refine_class_accessor_property_types(
    &mut self,
  ) -> Result<(), FatalError> {
    let store = Arc::clone(&self.store);
    let prim = store.primitive_ids();

    #[derive(Clone, Copy)]
    struct AccessorPatch {
      is_static: bool,
      is_getter: bool,
      def: DefId,
    }

    let mut by_class: HashMap<DefId, Vec<(String, AccessorPatch)>> = HashMap::new();
    let mut accessor_defs: Vec<(DefId, FileId)> = Vec::new();
    for (def, data) in self.def_data.iter() {
      if !matches!(data.kind, DefKind::Function(_)) {
        continue;
      }
      accessor_defs.push((*def, data.file));
    }
    accessor_defs.sort_by_key(|(def, file)| (file.0, def.0));

    for (def, file) in accessor_defs {
      let Some(lowered) = self.hir_lowered.get(&file) else {
        continue;
      };
      let Some(hir_def) = lowered.def(def) else {
        continue;
      };
      let is_getter = matches!(hir_def.path.kind, HirDefKind::Getter);
      let is_setter = matches!(hir_def.path.kind, HirDefKind::Setter);
      if !is_getter && !is_setter {
        continue;
      }
      let Some(parent) = hir_def.parent else {
        continue;
      };
      let Some(parent_def) = lowered.def(parent) else {
        continue;
      };
      if parent_def.path.kind != HirDefKind::Class {
        continue;
      }
      let Some(name) = lowered.names.resolve(hir_def.name) else {
        continue;
      };
      if name.is_empty() {
        continue;
      }
      by_class.entry(parent).or_default().push((
        name.to_string(),
        AccessorPatch {
          is_static: hir_def.is_static,
          is_getter,
          def,
        },
      ));
    }

    if by_class.is_empty() {
      return Ok(());
    }

    let mut class_ids: Vec<DefId> = by_class.keys().copied().collect();
    class_ids.sort_by_key(|id| id.0);

    for class_def in class_ids {
      let Some(accessors) = by_class.get(&class_def).cloned() else {
        continue;
      };

      let mut instance_patches: HashMap<String, TypeId> = HashMap::new();
      let mut static_patches: HashMap<String, TypeId> = HashMap::new();

      for (name, patch) in accessors {
        let fn_ty = self.type_of_def(patch.def)?;
        let prop_ty = if patch.is_getter {
          callable_return_type(&store, fn_ty).unwrap_or(prim.unknown)
        } else {
          callable_first_param_type(&store, fn_ty).unwrap_or(prim.unknown)
        };
        if matches!(
          store.type_kind(store.canon(prop_ty)),
          tti::TypeKind::Unknown
        ) {
          continue;
        }
        let target = if patch.is_static {
          &mut static_patches
        } else {
          &mut instance_patches
        };
        target
          .entry(name)
          .and_modify(|existing| {
            *existing = store.intersection(vec![*existing, prop_ty]);
          })
          .or_insert(prop_ty);
      }

      if instance_patches.is_empty() && static_patches.is_empty() {
        continue;
      }

      if let Some(instance_ty) = self.interned_def_types.get(&class_def).copied() {
        let patched = patch_unknown_object_props(&store, instance_ty, &instance_patches);
        if patched != instance_ty {
          self.interned_def_types.insert(class_def, patched);
          if let Some(value_def) = self.value_defs.get(&class_def).copied() {
            if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
              let new_value = patch_construct_returns_and_static_props(
                &store,
                value_ty,
                instance_ty,
                patched,
                &static_patches,
              );
              self.interned_def_types.insert(value_def, new_value);
            }
          }
        } else if !static_patches.is_empty() {
          if let Some(value_def) = self.value_defs.get(&class_def).copied() {
            if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
              let new_value = patch_unknown_object_props(&store, value_ty, &static_patches);
              self.interned_def_types.insert(value_def, new_value);
            }
          }
        }
      }
    }

    self.checker_caches.invalidate_shared();
    Ok(())
  }

  /// Infer unannotated class method return types and stamp them onto instance /
  /// constructor shapes.
  ///
  /// HIR class lowering uses `any` for missing return annotations, so
  /// `static getInstance() { return new C(); }` stayed `() => any` and
  /// `C.getInstance().#priv` skipped TS18013 (`any` short-circuits private
  /// visibility). Mirror accessor refine: `type_of_def` on the method body,
  /// then patch callable properties whose return is `any`/`unknown`.
  pub(in super::super) fn refine_class_method_property_types(&mut self) -> Result<(), FatalError> {
    let store = Arc::clone(&self.store);

    #[derive(Clone, Copy)]
    struct MethodPatch {
      is_static: bool,
      def: DefId,
    }

    let mut by_class: HashMap<DefId, Vec<(String, MethodPatch)>> = HashMap::new();
    let mut method_defs: Vec<(DefId, FileId)> = Vec::new();
    for (def, data) in self.def_data.iter() {
      if !matches!(data.kind, DefKind::Function(_)) {
        continue;
      }
      method_defs.push((*def, data.file));
    }
    method_defs.sort_by_key(|(def, file)| (file.0, def.0));

    for (def, file) in method_defs {
      let Some(lowered) = self.hir_lowered.get(&file) else {
        continue;
      };
      let Some(hir_def) = lowered.def(def) else {
        continue;
      };
      if hir_def.path.kind != HirDefKind::Method {
        continue;
      }
      let Some(parent) = hir_def.parent else {
        continue;
      };
      let Some(parent_def) = lowered.def(parent) else {
        continue;
      };
      if parent_def.path.kind != HirDefKind::Class {
        continue;
      }
      let Some(name) = lowered.names.resolve(hir_def.name) else {
        continue;
      };
      if name.is_empty() {
        continue;
      }
      by_class.entry(parent).or_default().push((
        name.to_string(),
        MethodPatch {
          is_static: hir_def.is_static,
          def,
        },
      ));
    }

    if by_class.is_empty() {
      return Ok(());
    }

    let mut class_ids: Vec<DefId> = by_class.keys().copied().collect();
    class_ids.sort_by_key(|id| id.0);

    for class_def in class_ids {
      let Some(methods) = by_class.get(&class_def).cloned() else {
        continue;
      };

      // Resolve well-known-symbol computed keys (`[Symbol.iterator]`) per
      // method def. Their def name is a synthetic `<computed:…>` fingerprint,
      // so the string-keyed patch maps below can never match the shape's
      // `PropKey::Symbol` properties; without this, inferred returns for such
      // methods (e.g. `[Symbol.iterator]() { return this; }`) stayed
      // `() => any` in class instance shapes (`iteratorSpreadInArray7.ts`).
      let mut sym_names: HashMap<DefId, String> = HashMap::new();
      let class_file = methods
        .first()
        .and_then(|(_, patch)| self.def_data.get(&patch.def).map(|data| data.file));
      if let Some(class_file) = class_file {
        if let Some(lowered) = self.hir_lowered.get(&class_file) {
          if let Some(hir_class) = lowered.def(class_def) {
            if let Some(body) = hir_class.body.and_then(|body_id| lowered.body(body_id)) {
              if let Some(class) = body.class.as_ref() {
                for member in class.members.iter() {
                  let hir_js::ClassMemberKind::Method { def, key, .. } = &member.kind else {
                    continue;
                  };
                  let hir_js::ClassMemberKey::Computed(expr_id) = key else {
                    continue;
                  };
                  let Some(expr) = body.exprs.get(expr_id.0 as usize) else {
                    continue;
                  };
                  let hir_js::ExprKind::Member(member_expr) = &expr.kind else {
                    continue;
                  };
                  let Some(object) = body.exprs.get(member_expr.object.0 as usize) else {
                    continue;
                  };
                  let hir_js::ExprKind::Ident(object_name) = &object.kind else {
                    continue;
                  };
                  if lowered.names.resolve(*object_name) != Some("Symbol") {
                    continue;
                  }
                  let sym = match &member_expr.property {
                    hir_js::ObjectKey::Ident(prop) => {
                      lowered.names.resolve(*prop).map(str::to_string)
                    }
                    hir_js::ObjectKey::String(name) => Some(name.clone()),
                    _ => None,
                  };
                  if let Some(sym) = sym {
                    sym_names.insert(*def, sym);
                  }
                }
              }
            }
          }
        }
      }

      let mut instance_patches: HashMap<String, TypeId> = HashMap::new();
      let mut static_patches: HashMap<String, TypeId> = HashMap::new();
      let mut instance_sym_patches: HashMap<String, TypeId> = HashMap::new();
      let mut static_sym_patches: HashMap<String, TypeId> = HashMap::new();

      for (name, patch) in &methods {
        let fn_ty = self.type_of_def(patch.def)?;
        let fn_ty = store.canon(fn_ty);
        if !matches!(store.type_kind(fn_ty), tti::TypeKind::Callable { .. }) {
          continue;
        }
        let Some(ret) = callable_return_type(&store, fn_ty) else {
          continue;
        };
        // Only stamp when we inferred something more precise than any/unknown.
        if matches!(
          store.type_kind(store.canon(ret)),
          tti::TypeKind::Unknown | tti::TypeKind::Any
        ) {
          continue;
        }
        if let Some(sym) = sym_names.get(&patch.def) {
          let target = if patch.is_static {
            &mut static_sym_patches
          } else {
            &mut instance_sym_patches
          };
          target
            .entry(sym.clone())
            .and_modify(|existing| {
              *existing = store.intersection(vec![*existing, fn_ty]);
            })
            .or_insert(fn_ty);
          continue;
        }
        let target = if patch.is_static {
          &mut static_patches
        } else {
          &mut instance_patches
        };
        target
          .entry(name.clone())
          .and_modify(|existing| {
            *existing = store.intersection(vec![*existing, fn_ty]);
          })
          .or_insert(fn_ty);
      }

      if instance_patches.is_empty()
        && static_patches.is_empty()
        && instance_sym_patches.is_empty()
        && static_sym_patches.is_empty()
      {
        continue;
      }

      if let Some(instance_ty) = self.interned_def_types.get(&class_def).copied() {
        let patched = patch_any_unknown_callable_props(
          &store,
          instance_ty,
          &instance_patches,
          &instance_sym_patches,
        );
        if patched != instance_ty {
          self.interned_def_types.insert(class_def, patched);
        }
        if let Some(value_def) = self.value_defs.get(&class_def).copied() {
          if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
            let new_value = if patched != instance_ty {
              patch_construct_returns_and_static_callable_props(
                &store,
                value_ty,
                instance_ty,
                patched,
                &static_patches,
                &static_sym_patches,
              )
            } else {
              patch_any_unknown_callable_props(
                &store,
                value_ty,
                &static_patches,
                &static_sym_patches,
              )
            };
            let new_value = rewrite_stale_constructor_self_returns(&store, new_value);
            if new_value != value_ty {
              self.interned_def_types.insert(value_def, new_value);
            }
            // Keep method DefId callables in sync (`type_of_def(getClass)`).
            for (_, patch) in methods.iter().filter(|(_, p)| p.is_static) {
              if let Some(fn_ty) = self.interned_def_types.get(&patch.def).copied() {
                let rewritten = rewrite_callable_stale_constructor_return(&store, fn_ty, new_value);
                if rewritten != fn_ty {
                  self.interned_def_types.insert(patch.def, rewritten);
                }
              }
            }
          }
        }
      } else if !static_patches.is_empty() || !static_sym_patches.is_empty() {
        if let Some(value_def) = self.value_defs.get(&class_def).copied() {
          if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
            let mut new_value = patch_any_unknown_callable_props(
              &store,
              value_ty,
              &static_patches,
              &static_sym_patches,
            );
            new_value = rewrite_stale_constructor_self_returns(&store, new_value);
            if new_value != value_ty {
              self.interned_def_types.insert(value_def, new_value);
            }
            for (_, patch) in methods.iter().filter(|(_, p)| p.is_static) {
              if let Some(fn_ty) = self.interned_def_types.get(&patch.def).copied() {
                let rewritten = rewrite_callable_stale_constructor_return(&store, fn_ty, new_value);
                if rewritten != fn_ty {
                  self.interned_def_types.insert(patch.def, rewritten);
                }
              }
            }
          }
        }
      }
    }

    self.checker_caches.invalidate_shared();
    Ok(())
  }

  /// Fill class field property types from initializer inference.
  ///
  /// `ClassMemberSig` only carries explicit annotations, so unannotated
  /// `three = 3` (and numeric keys like `1 = ''`) lowered as `unknown` in
  /// instance shapes; reads through the declared instance type (`var c: C;
  /// c.three`, `c[1]`) stayed `unknown` while the field defs themselves
  /// inferred fine — surfacing as TS2403 cascades on same-name `var`
  /// redeclarations (`numericIndexingResults.ts`). Mirrors the accessor
  /// refine: `type_of_def` on the field, then patch still-`unknown` instance /
  /// static shape properties (annotated fields keep their declared type).
  pub(in super::super) fn refine_class_field_property_types(&mut self) -> Result<(), FatalError> {
    let store = Arc::clone(&self.store);

    #[derive(Clone, Copy)]
    struct FieldPatch {
      is_static: bool,
      def: DefId,
    }

    let mut by_class: HashMap<DefId, Vec<(String, FieldPatch)>> = HashMap::new();
    let mut field_defs: Vec<(DefId, FileId)> = Vec::new();
    for (def, data) in self.def_data.iter() {
      // Class fields surface as `DefKind::Var` at the binder level; the HIR
      // path kind below discriminates them from ordinary variables.
      if !matches!(data.kind, DefKind::Var(_)) {
        continue;
      }
      field_defs.push((*def, data.file));
    }
    field_defs.sort_by_key(|(def, file)| (file.0, def.0));

    for (def, file) in field_defs {
      let Some(lowered) = self.hir_lowered.get(&file) else {
        continue;
      };
      let Some(hir_def) = lowered.def(def) else {
        continue;
      };
      if hir_def.path.kind != HirDefKind::Field {
        continue;
      }
      let Some(parent) = hir_def.parent else {
        continue;
      };
      let Some(parent_def) = lowered.def(parent) else {
        continue;
      };
      if parent_def.path.kind != HirDefKind::Class {
        continue;
      }
      let Some(name) = lowered.names.resolve(hir_def.name) else {
        continue;
      };
      if name.is_empty() {
        continue;
      }
      by_class.entry(parent).or_default().push((
        name.to_string(),
        FieldPatch {
          is_static: hir_def.is_static,
          def,
        },
      ));
    }

    if by_class.is_empty() {
      return Ok(());
    }

    let mut class_ids: Vec<DefId> = by_class.keys().copied().collect();
    class_ids.sort_by_key(|id| id.0);

    for class_def in class_ids {
      let Some(fields) = by_class.get(&class_def).cloned() else {
        continue;
      };

      let mut instance_patches: HashMap<String, TypeId> = HashMap::new();
      let mut static_patches: HashMap<String, TypeId> = HashMap::new();

      for (name, patch) in fields {
        let field_ty = store.canon(self.type_of_def(patch.def)?);
        // Only stamp when inference produced something more precise than
        // any/unknown.
        if matches!(
          store.type_kind(field_ty),
          tti::TypeKind::Unknown | tti::TypeKind::Any
        ) {
          continue;
        }
        let target = if patch.is_static {
          &mut static_patches
        } else {
          &mut instance_patches
        };
        target.entry(name).or_insert(field_ty);
      }

      if instance_patches.is_empty() && static_patches.is_empty() {
        continue;
      }

      if let Some(instance_ty) = self.interned_def_types.get(&class_def).copied() {
        let patched = patch_unknown_object_props(&store, instance_ty, &instance_patches);
        if patched != instance_ty {
          self.interned_def_types.insert(class_def, patched);
        }
        if let Some(value_def) = self.value_defs.get(&class_def).copied() {
          if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
            let new_value = if patched != instance_ty {
              patch_construct_returns_and_static_props(
                &store,
                value_ty,
                instance_ty,
                patched,
                &static_patches,
              )
            } else {
              patch_unknown_object_props(&store, value_ty, &static_patches)
            };
            if new_value != value_ty {
              self.interned_def_types.insert(value_def, new_value);
            }
          }
        }
      } else if !static_patches.is_empty() {
        if let Some(value_def) = self.value_defs.get(&class_def).copied() {
          if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
            let new_value = patch_unknown_object_props(&store, value_ty, &static_patches);
            if new_value != value_ty {
              self.interned_def_types.insert(value_def, new_value);
            }
          }
        }
      }
    }

    self.checker_caches.invalidate_shared();
    Ok(())
  }
}

fn callable_return_type(store: &tti::TypeStore, ty: TypeId) -> Option<TypeId> {
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Callable { overloads } => {
      let first = *overloads.first()?;
      Some(store.signature(first).ret)
    }
    _ => None,
  }
}

fn callable_first_param_type(store: &tti::TypeStore, ty: TypeId) -> Option<TypeId> {
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Callable { overloads } => {
      let first = *overloads.first()?;
      let sig = store.signature(first);
      Some(sig.params.first()?.ty)
    }
    _ => None,
  }
}

pub(super) fn patch_unknown_object_props(
  store: &tti::TypeStore,
  ty: TypeId,
  patches: &HashMap<String, TypeId>,
) -> TypeId {
  if patches.is_empty() {
    return ty;
  }
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Object(obj) => {
      let mut shape = store.shape(store.object(obj).shape);
      let mut changed = false;
      for prop in shape.properties.iter_mut() {
        let name = match &prop.key {
          PropKey::String(name_id) => store.name(*name_id),
          // Numeric-keyed members (`1 = ''`) are stored as `PropKey::Number`
          // while their def names are the source spelling (`"1"`).
          PropKey::Number(num) => num.to_string(),
          _ => continue,
        };
        let Some(patch_ty) = patches.get(&name).copied() else {
          continue;
        };
        if matches!(
          store.type_kind(store.canon(prop.data.ty)),
          tti::TypeKind::Unknown
        ) {
          prop.data.ty = store.canon(patch_ty);
          changed = true;
        }
      }
      if !changed {
        return ty;
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      store.intern_type(tti::TypeKind::Object(obj_id))
    }
    tti::TypeKind::Intersection(members) => {
      let mut out = Vec::with_capacity(members.len());
      let mut changed = false;
      for member in members {
        let patched = patch_unknown_object_props(store, member, patches);
        changed |= patched != member;
        out.push(patched);
      }
      if changed {
        store.intersection(out)
      } else {
        ty
      }
    }
    _ => ty,
  }
}

/// Replace object properties that are callables with `any`/`unknown` returns
/// (or bare `any`/`unknown`) using inferred method types.
fn patch_any_unknown_callable_props(
  store: &tti::TypeStore,
  ty: TypeId,
  patches: &HashMap<String, TypeId>,
  sym_patches: &HashMap<String, TypeId>,
) -> TypeId {
  if patches.is_empty() && sym_patches.is_empty() {
    return ty;
  }
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Object(obj) => {
      let mut shape = store.shape(store.object(obj).shape);
      let mut changed = false;
      for prop in shape.properties.iter_mut() {
        let patch_ty = match prop.key {
          PropKey::String(name_id) => patches.get(&store.name(name_id)),
          PropKey::Symbol(name_id) => {
            let name = store.name(name_id);
            sym_patches.get(&name).or_else(|| {
              name
                .strip_prefix("Symbol.")
                .and_then(|stripped| sym_patches.get(stripped))
            })
          }
          _ => None,
        };
        let Some(patch_ty) = patch_ty.copied() else {
          continue;
        };
        if callable_return_is_any_or_unknown(store, prop.data.ty) {
          prop.data.ty = store.canon(patch_ty);
          prop.data.is_method = true;
          changed = true;
        }
      }
      if !changed {
        return ty;
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      store.intern_type(tti::TypeKind::Object(obj_id))
    }
    tti::TypeKind::Intersection(members) => {
      let mut out = Vec::with_capacity(members.len());
      let mut changed = false;
      for member in members {
        let patched = patch_any_unknown_callable_props(store, member, patches, sym_patches);
        changed |= patched != member;
        out.push(patched);
      }
      if changed {
        store.intersection(out)
      } else {
        ty
      }
    }
    _ => ty,
  }
}

fn callable_return_is_any_or_unknown(store: &tti::TypeStore, ty: TypeId) -> bool {
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Any | tti::TypeKind::Unknown => true,
    tti::TypeKind::Callable { overloads } => overloads.iter().any(|sig_id| {
      matches!(
        store.type_kind(store.canon(store.signature(*sig_id).ret)),
        tti::TypeKind::Any | tti::TypeKind::Unknown
      )
    }),
    _ => false,
  }
}

/// Property names on an object type (string keys only).
fn object_prop_names(store: &tti::TypeStore, ty: TypeId) -> HashSet<String> {
  let mut out = HashSet::new();
  let ty = store.canon(ty);
  let tti::TypeKind::Object(obj) = store.type_kind(ty) else {
    return out;
  };
  let shape = store.shape(store.object(obj).shape);
  for prop in shape.properties.iter() {
    if let PropKey::String(name_id) = prop.key {
      out.insert(store.name(name_id));
    }
  }
  out
}

fn object_has_construct_sig(store: &tti::TypeStore, ty: TypeId) -> bool {
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Object(obj) => !store
      .shape(store.object(obj).shape)
      .construct_signatures
      .is_empty(),
    _ => false,
  }
}

/// Circular `static getClass() { return AA; }` freezes a structural snapshot of
/// `AA` taken before method returns were refined (`#m => any`). After the class
/// value is finalized, rewrite those self-returns to the final constructor type
/// (tsc `typeof AA`).
fn is_stale_constructor_snapshot(
  store: &tti::TypeStore,
  candidate: TypeId,
  value_ty: TypeId,
  value_keys: &HashSet<String>,
) -> bool {
  let candidate = store.canon(candidate);
  let value_ty = store.canon(value_ty);
  if candidate == value_ty {
    return false;
  }
  if !object_has_construct_sig(store, candidate) || !object_has_construct_sig(store, value_ty) {
    return false;
  }
  let cand_keys = object_prop_names(store, candidate);
  !cand_keys.is_empty() && cand_keys.is_subset(value_keys)
}

fn rewrite_callable_stale_constructor_return(
  store: &tti::TypeStore,
  fn_ty: TypeId,
  value_ty: TypeId,
) -> TypeId {
  let fn_ty = store.canon(fn_ty);
  let value_ty = store.canon(value_ty);
  let value_keys = object_prop_names(store, value_ty);
  let tti::TypeKind::Callable { overloads } = store.type_kind(fn_ty) else {
    return fn_ty;
  };
  let mut new_overloads = Vec::with_capacity(overloads.len());
  let mut changed = false;
  for sig_id in overloads.iter().copied() {
    let mut sig = store.signature(sig_id);
    let ret = store.canon(sig.ret);
    if is_stale_constructor_snapshot(store, ret, value_ty, &value_keys) {
      sig.ret = value_ty;
      new_overloads.push(store.intern_signature(sig));
      changed = true;
    } else {
      new_overloads.push(sig_id);
    }
  }
  if !changed {
    return fn_ty;
  }
  store.intern_type(tti::TypeKind::Callable {
    overloads: new_overloads,
  })
}

fn rewrite_stale_constructor_self_returns(store: &tti::TypeStore, value_ty: TypeId) -> TypeId {
  let value_ty = store.canon(value_ty);
  let tti::TypeKind::Object(obj) = store.type_kind(value_ty) else {
    return value_ty;
  };
  if !object_has_construct_sig(store, value_ty) {
    return value_ty;
  }
  let mut shape = store.shape(store.object(obj).shape);
  let mut changed = false;
  for prop in shape.properties.iter_mut() {
    let rewritten = rewrite_callable_stale_constructor_return(store, prop.data.ty, value_ty);
    if rewritten != store.canon(prop.data.ty) {
      prop.data.ty = rewritten;
      changed = true;
    }
  }
  // One fixed-point pass: methods rewritten above may still embed stale nested
  // self-returns via other props; rebuild once with the same value_ty target.
  if !changed {
    return value_ty;
  }
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
  let mid = store.intern_type(tti::TypeKind::Object(obj_id));
  // Re-walk against the *final* mid type as the self-return target.
  let mid = store.canon(mid);
  let tti::TypeKind::Object(obj) = store.type_kind(mid) else {
    return mid;
  };
  let mut shape = store.shape(store.object(obj).shape);
  let mut changed2 = false;
  for prop in shape.properties.iter_mut() {
    let rewritten = rewrite_callable_stale_constructor_return(store, prop.data.ty, mid);
    if rewritten != store.canon(prop.data.ty) {
      prop.data.ty = rewritten;
      changed2 = true;
    }
  }
  if !changed2 {
    return mid;
  }
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
  store.intern_type(tti::TypeKind::Object(obj_id))
}

fn patch_construct_returns_and_static_callable_props(
  store: &tti::TypeStore,
  value_ty: TypeId,
  old_instance: TypeId,
  new_instance: TypeId,
  static_patches: &HashMap<String, TypeId>,
  static_sym_patches: &HashMap<String, TypeId>,
) -> TypeId {
  let value_ty = store.canon(value_ty);
  let tti::TypeKind::Object(obj) = store.type_kind(value_ty) else {
    return patch_any_unknown_callable_props(store, value_ty, static_patches, static_sym_patches);
  };
  let mut shape = store.shape(store.object(obj).shape);
  let mut changed = false;

  for prop in shape.properties.iter_mut() {
    let patch_ty = match prop.key {
      PropKey::String(name_id) => static_patches.get(&store.name(name_id)),
      PropKey::Symbol(name_id) => {
        let name = store.name(name_id);
        static_sym_patches.get(&name).or_else(|| {
          name
            .strip_prefix("Symbol.")
            .and_then(|stripped| static_sym_patches.get(stripped))
        })
      }
      _ => None,
    };
    let Some(patch_ty) = patch_ty.copied() else {
      continue;
    };
    if callable_return_is_any_or_unknown(store, prop.data.ty) {
      prop.data.ty = store.canon(patch_ty);
      prop.data.is_method = true;
      changed = true;
    }
  }

  let mut new_ctors = Vec::with_capacity(shape.construct_signatures.len());
  for sig_id in shape.construct_signatures.iter().copied() {
    let mut sig = store.signature(sig_id);
    if store.canon(sig.ret) == store.canon(old_instance) {
      sig.ret = new_instance;
      new_ctors.push(store.intern_signature(sig));
      changed = true;
    } else {
      new_ctors.push(sig_id);
    }
  }
  if changed {
    shape.construct_signatures = new_ctors;
    let shape_id = store.intern_shape(shape);
    let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
    store.intern_type(tti::TypeKind::Object(obj_id))
  } else {
    value_ty
  }
}

fn patch_construct_returns_and_static_props(
  store: &tti::TypeStore,
  value_ty: TypeId,
  old_instance: TypeId,
  new_instance: TypeId,
  static_patches: &HashMap<String, TypeId>,
) -> TypeId {
  let value_ty = store.canon(value_ty);
  let tti::TypeKind::Object(obj) = store.type_kind(value_ty) else {
    return patch_unknown_object_props(store, value_ty, static_patches);
  };
  let mut shape = store.shape(store.object(obj).shape);
  let mut changed = false;

  // Static accessor properties on the constructor object.
  for prop in shape.properties.iter_mut() {
    let name = match &prop.key {
      PropKey::String(name_id) => store.name(*name_id),
      PropKey::Number(num) => num.to_string(),
      _ => continue,
    };
    let Some(patch_ty) = static_patches.get(&name).copied() else {
      continue;
    };
    if matches!(
      store.type_kind(store.canon(prop.data.ty)),
      tti::TypeKind::Unknown
    ) {
      prop.data.ty = store.canon(patch_ty);
      changed = true;
    }
  }

  let mut new_ctors = Vec::with_capacity(shape.construct_signatures.len());
  for sig_id in shape.construct_signatures.iter().copied() {
    let mut sig = store.signature(sig_id);
    if store.canon(sig.ret) == store.canon(old_instance) {
      sig.ret = new_instance;
      new_ctors.push(store.intern_signature(sig));
      changed = true;
    } else {
      new_ctors.push(sig_id);
    }
  }
  if changed {
    shape.construct_signatures = new_ctors;
    let shape_id = store.intern_shape(shape);
    let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
    store.intern_type(tti::TypeKind::Object(obj_id))
  } else {
    value_ty
  }
}
