use super::accessor_refine::patch_unknown_object_props;
use super::*;
use hir_js::{
  AssignOp, ClassMemberKind, ExprId as HirExprId, ExprKind as HirExprKind, Literal, ObjectKey,
  PatId as HirPatId, PatKind as HirPatKind, StmtId as HirStmtId, StmtKind as HirStmtKind,
};

impl ProgramState {
  /// Infer unannotated static field types from `this.prop = …` / field
  /// initializers in source order (tsc class static evaluation order).
  ///
  /// Without this, `static x;` + `static { this.x = 1; }` stayed `unknown` and
  /// `--noImplicitAny` emitted spurious **TC3000** (e.g.
  /// `classStaticBlockUseBeforeDef1`).
  pub(in super::super) fn refine_class_static_field_types_from_assignments(
    &mut self,
  ) -> Result<(), FatalError> {
    let store = Arc::clone(&self.store);
    let prim = store.primitive_ids();

    let mut class_defs: Vec<(DefId, FileId)> = Vec::new();
    for (def, data) in self.def_data.iter() {
      if matches!(data.kind, DefKind::Class(_)) {
        class_defs.push((*def, data.file));
      }
    }
    class_defs.sort_by_key(|(def, file)| (file.0, def.0));

    for (class_def, file) in class_defs {
      self.check_cancelled()?;
      let Some(lowered) = self.hir_lowered.get(&file).cloned() else {
        continue;
      };
      let Some(hir_class) = lowered.def(class_def) else {
        continue;
      };
      if hir_class.path.kind != HirDefKind::Class {
        continue;
      }
      let Some(class_body_id) = hir_class.body else {
        continue;
      };
      let Some(class_body) = lowered.body(class_body_id) else {
        continue;
      };
      let Some(class_meta) = class_body.class.as_ref() else {
        continue;
      };

      let class_name = lowered.names.resolve(hir_class.name).map(|s| s.to_string());

      // Seed with already-known (annotated / previously inferred) static props.
      let mut prop_tys: HashMap<String, TypeId> = HashMap::new();
      if let Some(value_def) = self.value_defs.get(&class_def).copied() {
        if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
          collect_object_prop_tys(&store, value_ty, &mut prop_tys);
        }
      }

      let mut field_defs: HashMap<String, DefId> = HashMap::new();
      let mut inferred_patches: HashMap<String, TypeId> = HashMap::new();

      for member in class_meta.members.iter() {
        if !member.static_ {
          continue;
        }
        match &member.kind {
          ClassMemberKind::Field {
            def: field_def,
            initializer,
            key,
          } => {
            let Some(name) = member_key_name(&lowered, key) else {
              continue;
            };
            field_defs.insert(name.clone(), *field_def);

            let has_annotation = lowered
              .def(*field_def)
              .and_then(|d| d.declared_type)
              .is_some()
              || matches!(
                self.def_data.get(field_def).map(|d| &d.kind),
                Some(DefKind::Var(v)) if v.typ.is_some()
              );

            if has_annotation {
              if let Some(ty) = self.hir_declared_type_for_def(*field_def).or_else(|| {
                self.def_data.get(field_def).and_then(|d| match &d.kind {
                  DefKind::Var(v) => v.typ,
                  _ => None,
                })
              }) {
                if !matches!(
                  store.type_kind(store.canon(ty)),
                  tti::TypeKind::Unknown | tti::TypeKind::Any
                ) {
                  prop_tys.insert(name, store.canon(ty));
                }
              }
              continue;
            }

            // Prefer an existing non-unknown prop type (e.g. from class shape).
            if let Some(existing) = prop_tys.get(&name).copied() {
              if !matches!(
                store.type_kind(store.canon(existing)),
                tti::TypeKind::Unknown
              ) {
                continue;
              }
            }

            if let Some(init_body) = *initializer {
              if let Some(init_ty) =
                synth_initializer_ty(&lowered, init_body, &prop_tys, &class_name, &store)
              {
                let widened = crate::check::widen::widen_literal(store.as_ref(), init_ty);
                prop_tys.insert(name.clone(), widened);
                inferred_patches.insert(name, widened);
              }
            }
          }
          ClassMemberKind::StaticBlock { body, .. } => {
            let Some(block_body) = lowered.body(*body) else {
              continue;
            };
            let mut assigns: Vec<(String, TypeId)> = Vec::new();
            for stmt_id in block_body.root_stmts.iter().copied() {
              collect_static_this_assigns(
                &lowered,
                block_body,
                stmt_id,
                &prop_tys,
                &class_name,
                &store,
                &mut assigns,
              );
            }
            for (name, ty) in assigns {
              let widened = crate::check::widen::widen_literal(store.as_ref(), ty);
              // First definite assignment wins for the property type (tsc).
              if !prop_tys.contains_key(&name)
                || matches!(
                  store.type_kind(store.canon(prop_tys[&name])),
                  tti::TypeKind::Unknown
                )
              {
                prop_tys.insert(name.clone(), widened);
                inferred_patches.insert(name, widened);
              }
            }
          }
          _ => {}
        }
      }

      if inferred_patches.is_empty() {
        continue;
      }

      // Stamp inferred types onto field defs so `type_of_def` does not TC3000.
      for (name, ty) in inferred_patches.iter() {
        let Some(field_def) = field_defs.get(name).copied() else {
          continue;
        };
        if let Some(data) = self.def_data.get_mut(&field_def) {
          if let DefKind::Var(var) = &mut data.kind {
            if var.typ.is_none()
              || matches!(
                store.type_kind(store.canon(var.typ.unwrap_or(prim.unknown))),
                tti::TypeKind::Unknown
              )
            {
              var.typ = Some(*ty);
            }
          }
        }
        self.interned_def_types.insert(field_def, *ty);
      }

      // Patch the constructor-object (static) shape so `this.prop` resolves.
      if let Some(value_def) = self.value_defs.get(&class_def).copied() {
        if let Some(value_ty) = self.interned_def_types.get(&value_def).copied() {
          let patched = patch_unknown_object_props(&store, value_ty, &inferred_patches);
          if patched != value_ty {
            self.interned_def_types.insert(value_def, patched);
          }
        }
      }
      if let Some(ClassData {
        static_type: Some(static_ty),
        ..
      }) = self.def_data.get(&class_def).and_then(|d| match &d.kind {
        DefKind::Class(c) => Some(c),
        _ => None,
      }) {
        let static_ty = *static_ty;
        let patched = patch_unknown_object_props(&store, static_ty, &inferred_patches);
        if patched != static_ty {
          if let Some(DefKind::Class(c)) = self.def_data.get_mut(&class_def).map(|d| &mut d.kind) {
            c.static_type = Some(patched);
          }
        }
      }
    }

    self.checker_caches.invalidate_shared();
    Ok(())
  }
}

fn member_key_name(lowered: &hir_js::LowerResult, key: &hir_js::ClassMemberKey) -> Option<String> {
  match key {
    hir_js::ClassMemberKey::Ident(id) | hir_js::ClassMemberKey::Private(id) => {
      lowered.names.resolve(*id).map(|s| s.to_string())
    }
    hir_js::ClassMemberKey::String(s) => Some(s.clone()),
    hir_js::ClassMemberKey::Number(s) => Some(s.clone()),
    hir_js::ClassMemberKey::Computed(_) => None,
  }
}

fn collect_object_prop_tys(store: &tti::TypeStore, ty: TypeId, out: &mut HashMap<String, TypeId>) {
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    tti::TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      for prop in shape.properties.iter() {
        let PropKey::String(name_id) = prop.key else {
          continue;
        };
        let name = store.name(name_id);
        if matches!(
          store.type_kind(store.canon(prop.data.ty)),
          tti::TypeKind::Unknown
        ) {
          continue;
        }
        out.entry(name).or_insert(store.canon(prop.data.ty));
      }
    }
    tti::TypeKind::Intersection(members) => {
      for member in members {
        collect_object_prop_tys(store, member, out);
      }
    }
    _ => {}
  }
}

fn synth_initializer_ty(
  lowered: &hir_js::LowerResult,
  body_id: hir_js::BodyId,
  prop_tys: &HashMap<String, TypeId>,
  class_name: &Option<String>,
  store: &tti::TypeStore,
) -> Option<TypeId> {
  let body = lowered.body(body_id)?;
  let mut expr = None;
  for stmt_id in body.root_stmts.iter().copied() {
    if let HirStmtKind::Expr(e) = &body.stmts.get(stmt_id.0 as usize)?.kind {
      expr = Some(*e);
      break;
    }
  }
  synth_expr_ty(lowered, body, expr?, prop_tys, class_name, store)
}

fn collect_static_this_assigns(
  lowered: &hir_js::LowerResult,
  body: &hir_js::Body,
  stmt_id: HirStmtId,
  prop_tys: &HashMap<String, TypeId>,
  class_name: &Option<String>,
  store: &tti::TypeStore,
  out: &mut Vec<(String, TypeId)>,
) {
  let Some(stmt) = body.stmts.get(stmt_id.0 as usize) else {
    return;
  };
  match &stmt.kind {
    HirStmtKind::Expr(expr) => {
      collect_assigns_in_expr(lowered, body, *expr, prop_tys, class_name, store, out);
    }
    HirStmtKind::Block(stmts) => {
      for child in stmts.iter().copied() {
        collect_static_this_assigns(lowered, body, child, prop_tys, class_name, store, out);
      }
    }
    HirStmtKind::If {
      consequent,
      alternate,
      ..
    } => {
      collect_static_this_assigns(lowered, body, *consequent, prop_tys, class_name, store, out);
      if let Some(alt) = *alternate {
        collect_static_this_assigns(lowered, body, alt, prop_tys, class_name, store, out);
      }
    }
    _ => {}
  }
}

fn collect_assigns_in_expr(
  lowered: &hir_js::LowerResult,
  body: &hir_js::Body,
  expr_id: HirExprId,
  prop_tys: &HashMap<String, TypeId>,
  class_name: &Option<String>,
  store: &tti::TypeStore,
  out: &mut Vec<(String, TypeId)>,
) {
  let Some(expr) = body.exprs.get(expr_id.0 as usize) else {
    return;
  };
  match &expr.kind {
    HirExprKind::Assignment {
      op: AssignOp::Assign,
      target,
      value,
    } => {
      if let Some(name) = static_assign_target_name(lowered, body, *target, class_name) {
        if let Some(ty) = synth_expr_ty(lowered, body, *value, prop_tys, class_name, store) {
          out.push((name, ty));
        }
      }
      collect_assigns_in_expr(lowered, body, *value, prop_tys, class_name, store, out);
    }
    HirExprKind::Binary { left, right, .. } => {
      collect_assigns_in_expr(lowered, body, *left, prop_tys, class_name, store, out);
      collect_assigns_in_expr(lowered, body, *right, prop_tys, class_name, store, out);
    }
    HirExprKind::Conditional {
      test,
      consequent,
      alternate,
    } => {
      collect_assigns_in_expr(lowered, body, *test, prop_tys, class_name, store, out);
      collect_assigns_in_expr(lowered, body, *consequent, prop_tys, class_name, store, out);
      collect_assigns_in_expr(lowered, body, *alternate, prop_tys, class_name, store, out);
    }
    HirExprKind::Unary { expr, .. } | HirExprKind::Update { expr, .. } => {
      collect_assigns_in_expr(lowered, body, *expr, prop_tys, class_name, store, out);
    }
    HirExprKind::Member(mem) => {
      collect_assigns_in_expr(lowered, body, mem.object, prop_tys, class_name, store, out);
    }
    HirExprKind::Call(call) => {
      collect_assigns_in_expr(lowered, body, call.callee, prop_tys, class_name, store, out);
      for arg in call.args.iter() {
        collect_assigns_in_expr(lowered, body, arg.expr, prop_tys, class_name, store, out);
      }
    }
    _ => {}
  }
}

fn static_assign_target_name(
  lowered: &hir_js::LowerResult,
  body: &hir_js::Body,
  pat_id: HirPatId,
  class_name: &Option<String>,
) -> Option<String> {
  let pat = body.pats.get(pat_id.0 as usize)?;
  let HirPatKind::AssignTarget(expr_id) = pat.kind else {
    return None;
  };
  let expr = body.exprs.get(expr_id.0 as usize)?;
  let HirExprKind::Member(mem) = &expr.kind else {
    return None;
  };
  let obj = body.exprs.get(mem.object.0 as usize)?;
  let obj_ok = match &obj.kind {
    HirExprKind::This => true,
    HirExprKind::Ident(name_id) => class_name.as_deref() == lowered.names.resolve(*name_id),
    _ => false,
  };
  if !obj_ok {
    return None;
  }
  match &mem.property {
    ObjectKey::Ident(name_id) => lowered.names.resolve(*name_id).map(|s| s.to_string()),
    ObjectKey::String(s) => Some(s.clone()),
    ObjectKey::Number(s) => Some(s.clone()),
    ObjectKey::Computed(_) => None,
  }
}

fn synth_expr_ty(
  lowered: &hir_js::LowerResult,
  body: &hir_js::Body,
  expr_id: HirExprId,
  prop_tys: &HashMap<String, TypeId>,
  class_name: &Option<String>,
  store: &tti::TypeStore,
) -> Option<TypeId> {
  let prim = store.primitive_ids();
  let expr = body.exprs.get(expr_id.0 as usize)?;
  match &expr.kind {
    HirExprKind::Literal(lit) => match lit {
      Literal::Number(_) => Some(prim.number),
      Literal::String(_) => Some(prim.string),
      Literal::Boolean(_) => Some(prim.boolean),
      Literal::Null => Some(prim.null),
      Literal::Undefined => Some(prim.undefined),
      Literal::BigInt(_) => Some(prim.bigint),
      Literal::Regex(_) => None,
    },
    HirExprKind::Member(mem) => {
      let obj = body.exprs.get(mem.object.0 as usize)?;
      let obj_ok = match &obj.kind {
        HirExprKind::This => true,
        HirExprKind::Ident(name_id) => class_name.as_deref() == lowered.names.resolve(*name_id),
        _ => false,
      };
      if !obj_ok {
        return None;
      }
      let name = match &mem.property {
        ObjectKey::Ident(name_id) => lowered.names.resolve(*name_id)?,
        ObjectKey::String(s) => s.as_str(),
        ObjectKey::Number(s) => s.as_str(),
        ObjectKey::Computed(_) => return None,
      };
      prop_tys
        .get(name)
        .copied()
        .filter(|ty| !matches!(store.type_kind(store.canon(*ty)), tti::TypeKind::Unknown))
    }
    HirExprKind::Unary {
      op: hir_js::UnaryOp::Minus | hir_js::UnaryOp::Plus,
      expr,
    } => {
      // `-1` / `+1` stay number.
      let inner = synth_expr_ty(lowered, body, *expr, prop_tys, class_name, store)?;
      matches!(store.type_kind(store.canon(inner)), tti::TypeKind::Number).then_some(prim.number)
    }
    _ => None,
  }
}
