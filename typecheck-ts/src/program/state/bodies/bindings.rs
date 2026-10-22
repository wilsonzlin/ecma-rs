use super::*;

impl ProgramState {
  pub(super) fn collect_parent_bindings(
    &mut self,
    body_id: BodyId,
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
  ) -> Result<(), FatalError> {
    self.check_cancelled()?;
    let store = Arc::clone(&self.store);
    let unknown = store.primitive_ids().unknown;
    fn record_pat(
      state: &mut ProgramState,
      pat_id: HirPatId,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      result: &BodyCheckResult,
      bindings: &mut HashMap<String, TypeId>,
      binding_defs: &mut HashMap<String, DefId>,
      file: FileId,
      store: &Arc<tti::TypeStore>,
      unknown: TypeId,
      seen: &mut HashSet<String>,
    ) {
      let Some(pat) = body.pats.get(pat_id.0 as usize) else {
        return;
      };
      let mut ty = result.pat_type(PatId(pat_id.0)).unwrap_or(unknown);
      if !store.contains_type_id(ty) {
        ty = store.primitive_ids().unknown;
      }
      match &pat.kind {
        HirPatKind::Ident(name_id) => {
          if let Some(name) = names.resolve(*name_id) {
            let name = name.to_string();
            if !seen.insert(name.clone()) {
              return;
            }

            let def_id = state
              .def_data
              .iter()
              .filter_map(|(id, data)| {
                if data.file != file || data.name != name {
                  return None;
                }
                if matches!(data.kind, DefKind::VarDeclarator(_)) {
                  return None;
                }
                if data.span == pat.span {
                  return Some((0_u8, data.span.len(), data.span.start, data.span.end, *id));
                }
                if data.span.start <= pat.span.start && data.span.end >= pat.span.end {
                  return Some((1_u8, data.span.len(), data.span.start, data.span.end, *id));
                }
                None
              })
              .min_by_key(|key| *key)
              .map(|(_, _, _, _, id)| id);

            if let Some(def_id) = def_id {
              binding_defs.insert(name.clone(), def_id);
            }

            // If this binding has an explicit type annotation, prefer the declared
            // type over the (possibly literal-inferred) pattern type from the parent
            // body. This matches TypeScript's behavior for e.g.
            // `const x: string = ""` where `x` should be `string`, not `""`.
            let should_prefer_declared = matches!(
              store.type_kind(ty),
              tti::TypeKind::Unknown
                | tti::TypeKind::StringLiteral(_)
                | tti::TypeKind::NumberLiteral(_)
                | tti::TypeKind::BooleanLiteral(_)
                | tti::TypeKind::BigIntLiteral(_)
            );
            if should_prefer_declared {
              let declared = state.declared_type_for_span(file, pat.span);
              if let Some(declared) = declared {
                if store.contains_type_id(declared) {
                  ty = store.canon(declared);
                }
              }
            }
            let replace = match bindings.get(&name) {
              None => true,
              Some(existing) => {
                if !store.contains_type_id(*existing)
                  || matches!(store.type_kind(*existing), tti::TypeKind::Unknown)
                {
                  true
                } else {
                  matches!(
                    (store.type_kind(*existing), store.type_kind(ty)),
                    (tti::TypeKind::StringLiteral(_), tti::TypeKind::String)
                      | (tti::TypeKind::NumberLiteral(_), tti::TypeKind::Number)
                      | (tti::TypeKind::BooleanLiteral(_), tti::TypeKind::Boolean)
                      | (tti::TypeKind::BigIntLiteral(_), tti::TypeKind::BigInt)
                  )
                }
              }
            };
            if replace {
              bindings.insert(name, ty);
            }
          }
        }
        HirPatKind::Array(arr) => {
          for elem in arr.elements.iter().flatten() {
            record_pat(
              state,
              elem.pat,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
          if let Some(rest) = arr.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
        }
        HirPatKind::Object(obj) => {
          for prop in obj.props.iter() {
            record_pat(
              state,
              prop.value,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
          if let Some(rest) = obj.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
              store,
              unknown,
              seen,
            );
          }
        }
        HirPatKind::Rest(inner) => {
          record_pat(
            state,
            **inner,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            store,
            unknown,
            seen,
          );
        }
        HirPatKind::Assign { target, .. } => {
          record_pat(
            state,
            *target,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
            store,
            unknown,
            seen,
          );
        }
        HirPatKind::AssignTarget(_) => {}
      }
    }

    let mut visited = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    if let Some(meta) = self.body_map.get(&body_id).copied() {
      if matches!(meta.kind, HirBodyKind::Initializer) {
        if let (Some(hir_id), Some(lowered)) = (meta.hir, self.hir_lowered.get(&meta.file)) {
          if let Some(hir_body) = lowered.body(hir_id) {
            if let Some(owner_def) = lowered.def(hir_body.owner) {
              if let Some(parent_def) = owner_def.parent {
                if let Some(parent_body) = lowered.def(parent_def).and_then(|def| def.body) {
                  if parent_body != body_id {
                    self.body_parents.insert(body_id, parent_body);
                    current = Some(parent_body);
                  }
                }
              }
            }
          }
        }
      }
    }
    // Named `class Foo` / `function Foo` expressions bind their name in the
    // class/function body (and nested member bodies). Seed those before outer
    // parent pats so the expression name shadows captured parameters.
    seed_enclosing_named_exprs(
      self,
      body_id,
      bindings,
      binding_defs,
      &mut seen_names,
      &store,
      unknown,
    );
    while let Some(parent) = current {
      self.check_cancelled()?;
      if !visited.insert(parent) {
        break;
      }
      let Some(meta) = self.body_map.get(&parent).copied() else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      if matches!(meta.kind, HirBodyKind::TopLevel)
        && self.files.get(&meta.file).and_then(|state| state.top_body) == Some(parent)
      {
        // Do not `check_body` the file top-level (avoids cycles / duplicate
        // work), but still seed nested `namespace` / block class·enum·…
        // decls. Those are not file-root bindings, yet class-body heritage
        // (`extends Base` inside `namespace Errors`) must resolve them
        // (`assignmentCompatWithCallSignatures4.ts`).
        //
        // Only enter blocks that enclose the body being checked, and let
        // those nested decls overwrite file-root same-named types
        // (`assignmentCompatWithNumericIndexer3.ts`).
        let child_span = self.body_map.get(&body_id).and_then(|meta| {
          let hir_id = meta.hir?;
          let lowered = self.hir_lowered.get(&meta.file)?;
          lowered.body(hir_id).map(|b| b.span)
        });
        if let Some(hir_body_id) = meta.hir {
          if let Some(lowered) = self.hir_lowered.get(&meta.file).cloned() {
            if let Some(body) = lowered.body(hir_body_id) {
              for stmt_id in body.root_stmts.iter().copied() {
                seed_type_decls_from_stmt(
                  self,
                  body,
                  stmt_id,
                  binding_defs,
                  &mut seen_names,
                  child_span,
                  false,
                );
              }
            }
          }
        }
        break;
      }
      let parent_result = self.check_body(parent)?;
      let Some(hir_body_id) = meta.hir else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file).cloned() else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(body) = lowered.body(hir_body_id) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      for pat in body.pats.iter().enumerate() {
        record_pat(
          self,
          HirPatId(pat.0 as u32),
          body,
          &lowered.names,
          &parent_result,
          bindings,
          binding_defs,
          meta.file,
          &store,
          unknown,
          &mut seen_names,
        );
      }
      // Nested `class` / `enum` / `interface` / `type` decls in parent bodies are
      // not file-level bindings, but TypeScript still resolves them as types in
      // inner scopes (e.g. `class Outer { ctor() { class Inner { m(x: Inner) {} } } }`).
      // Seed those DefIds into the body resolver so type annotations do not emit
      // false TC2008 / cascading TS2339.
      for stmt_id in body.root_stmts.iter().copied() {
        seed_type_decls_from_stmt(
          self,
          body,
          stmt_id,
          binding_defs,
          &mut seen_names,
          None,
          false,
        );
      }
      if parent_result.pat_types.is_empty() && matches!(meta.kind, HirBodyKind::Function) {
        // If we're checking a nested body while the parent is still being checked, `check_body`
        // returns an empty result to break cycles. Seed parameter bindings directly from the
        // owning function's annotations so initializer bodies can still resolve captured params.
        if let Some(owner) = self.owner_of_body(parent) {
          if let Some(DefData {
            kind: DefKind::Function(func),
            ..
          }) = self.def_data.get(&owner)
          {
            for param in func.params.iter() {
              if param.name.starts_with("<pattern") {
                continue;
              }
              let mapped = param
                .typ
                .filter(|ty| store.contains_type_id(*ty))
                .map(|ty| store.canon(ty))
                .unwrap_or_else(|| store.primitive_ids().unknown);
              bindings
                .entry(param.name.clone())
                .and_modify(|existing| {
                  let existing_unknown = !store.contains_type_id(*existing)
                    || matches!(store.type_kind(*existing), tti::TypeKind::Unknown);
                  if existing_unknown {
                    *existing = mapped;
                  }
                })
                .or_insert(mapped);
            }
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    // `seed_type_decls_from_stmt` only fills the type resolver map. Heritage
    // and `new C()` use value-namespace lookup — materialize class/enum ctor
    // types into `bindings` as well.
    let pending: Vec<(String, DefId)> = binding_defs
      .iter()
      .filter(|(name, def)| {
        !bindings.contains_key(*name)
          && self
            .def_data
            .get(def)
            .is_some_and(|data| matches!(data.kind, DefKind::Class(_) | DefKind::Enum(_)))
      })
      .map(|(name, def)| (name.clone(), *def))
      .collect();
    for (name, def) in pending {
      self.check_cancelled()?;
      if self.type_stack.contains(&def) {
        continue;
      }
      let ty = self
        .interned_def_types
        .get(&def)
        .copied()
        .filter(|ty| store.contains_type_id(*ty))
        .map(|ty| store.canon(ty))
        .filter(|ty| !matches!(store.type_kind(*ty), tti::TypeKind::Unknown));
      let ty = match ty {
        Some(ty) => Some(ty),
        None => match self.type_of_def(def) {
          Ok(ty) => Some(store.canon(ty)),
          Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
          Err(_) => None,
        },
      };
      if let Some(ty) = ty {
        if !matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
          bindings.insert(name, ty);
        }
      }
    }
    Ok(())
  }
}

/// Seed names of enclosing named `class` / `function` expressions into the
/// body being checked (tsc: class/function expression name is in scope for the
/// body and nested members). Walks `body_parents` nearest-first so an inner
/// expression name shadows outer ones and outer parameter captures.
fn seed_enclosing_named_exprs(
  state: &ProgramState,
  body_id: BodyId,
  bindings: &mut HashMap<String, TypeId>,
  binding_defs: &mut HashMap<String, DefId>,
  seen_names: &mut HashSet<String>,
  store: &Arc<tti::TypeStore>,
  unknown: TypeId,
) {
  let mut child = body_id;
  let mut current = state.body_parents.get(&body_id).copied();
  let mut visited = HashSet::new();
  while let Some(parent) = current {
    if !visited.insert(parent) {
      break;
    }
    let Some(meta) = state.body_map.get(&parent).copied() else {
      current = state.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    let Some(hir_id) = meta.hir else {
      current = state.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    let Some(lowered) = state.hir_lowered.get(&meta.file) else {
      current = state.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    let Some(parent_body) = lowered.body(hir_id) else {
      current = state.body_parents.get(&parent).copied();
      child = parent;
      continue;
    };
    for expr in parent_body.exprs.iter() {
      match &expr.kind {
        HirExprKind::ClassExpr { def, body, name } => {
          if *body != child {
            continue;
          }
          let Some(name_id) = *name else {
            continue;
          };
          let Some(name) = lowered.names.resolve(name_id) else {
            continue;
          };
          if name.is_empty() || name.starts_with('<') {
            continue;
          }
          if !seen_names.insert(name.to_string()) {
            continue;
          }
          // Type-side def for `x: D`; value-side ctor type for `new D()`.
          binding_defs.insert(name.to_string(), *def);
          if let Some(ty) = class_expr_ctor_ty(state, store, *def, expr.span) {
            bindings.insert(name.to_string(), ty);
          }
        }
        HirExprKind::FunctionExpr {
          def,
          body,
          name,
          is_arrow: false,
        } => {
          if *body != child {
            continue;
          }
          let Some(name_id) = *name else {
            continue;
          };
          let Some(name) = lowered.names.resolve(name_id) else {
            continue;
          };
          if name.is_empty() || name.starts_with('<') {
            continue;
          }
          if !seen_names.insert(name.to_string()) {
            continue;
          }
          binding_defs.insert(name.to_string(), *def);
          let ty = state
            .interned_def_types
            .get(def)
            .copied()
            .filter(|ty| store.contains_type_id(*ty))
            .map(|ty| store.canon(ty))
            .filter(|ty| !matches!(store.type_kind(*ty), tti::TypeKind::Unknown))
            .unwrap_or(unknown);
          if ty != unknown {
            bindings.insert(name.to_string(), ty);
          }
        }
        _ => {}
      }
    }
    current = state.body_parents.get(&parent).copied();
    child = parent;
  }
}

/// Constructor value type for a named class expression (value-side `DefId` /
/// same-span constructable interned type). Returns `None` when only `unknown`
/// is available so we do not poison value lookup.
fn class_expr_ctor_ty(
  state: &ProgramState,
  store: &Arc<tti::TypeStore>,
  type_def: DefId,
  expr_span: TextRange,
) -> Option<TypeId> {
  if let Some(value_def) = state.value_defs.get(&type_def).copied() {
    if let Some(ty) = state.interned_def_types.get(&value_def).copied() {
      if store.contains_type_id(ty) {
        let ty = store.canon(ty);
        if check::hir_body::type_has_construct_signature(store.as_ref(), ty) {
          return Some(ty);
        }
      }
    }
  }
  // Fallback: any same-span interned def with construct signatures (salsa path
  // equivalent when `value_defs` is not consulted).
  for (other_def, data) in state.def_data.iter() {
    if data.span != expr_span {
      continue;
    }
    if let Some(ty) = state.interned_def_types.get(other_def).copied() {
      if store.contains_type_id(ty) {
        let ty = store.canon(ty);
        if check::hir_body::type_has_construct_signature(store.as_ref(), ty) {
          return Some(ty);
        }
      }
    }
  }
  None
}

fn span_encloses(outer: TextRange, inner: TextRange) -> bool {
  outer.start <= inner.start && outer.end >= inner.end
}

pub(super) fn seed_type_decls_from_stmt(
  state: &ProgramState,
  body: &hir_js::Body,
  stmt_id: hir_js::StmtId,
  binding_defs: &mut HashMap<String, DefId>,
  seen_names: &mut HashSet<String>,
  enclosing: Option<TextRange>,
  in_enclosing_block: bool,
) {
  let Some(stmt) = body.stmts.get(stmt_id.0 as usize) else {
    return;
  };
  match &stmt.kind {
    hir_js::StmtKind::Decl(def_id) => {
      if enclosing.is_some() && !in_enclosing_block {
        return;
      }
      let Some(data) = state.def_data.get(def_id) else {
        return;
      };
      if data.name.is_empty() || data.name.starts_with('<') {
        return;
      }
      // Only TYPE-capable decls: nested functions are VALUE-only and do not
      // satisfy `resolve_local(..., Namespace::TYPE)`.
      if !matches!(
        data.kind,
        DefKind::Class(_) | DefKind::Enum(_) | DefKind::Interface(_) | DefKind::TypeAlias(_)
      ) {
        return;
      }
      if in_enclosing_block {
        seen_names.insert(data.name.clone());
        binding_defs.insert(data.name.clone(), *def_id);
        return;
      }
      // Prefer nearer parent scopes (walk order is nearest-first).
      if !seen_names.insert(data.name.clone()) {
        return;
      }
      binding_defs.insert(data.name.clone(), *def_id);
    }
    hir_js::StmtKind::Block(stmts) => {
      let child_in_block = match enclosing {
        Some(enc) if span_encloses(stmt.span, enc) => true,
        Some(_) => return,
        None => in_enclosing_block,
      };
      for child in stmts.iter().copied() {
        seed_type_decls_from_stmt(
          state,
          body,
          child,
          binding_defs,
          seen_names,
          enclosing,
          child_in_block,
        );
      }
    }
    hir_js::StmtKind::If {
      consequent,
      alternate,
      ..
    } => {
      seed_type_decls_from_stmt(
        state,
        body,
        *consequent,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
      if let Some(alt) = *alternate {
        seed_type_decls_from_stmt(
          state,
          body,
          alt,
          binding_defs,
          seen_names,
          enclosing,
          in_enclosing_block,
        );
      }
    }
    hir_js::StmtKind::While { body: inner, .. }
    | hir_js::StmtKind::DoWhile { body: inner, .. }
    | hir_js::StmtKind::For { body: inner, .. }
    | hir_js::StmtKind::ForIn { body: inner, .. } => {
      seed_type_decls_from_stmt(
        state,
        body,
        *inner,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
    }
    hir_js::StmtKind::Switch { cases, .. } => {
      for case in cases.iter() {
        for child in case.consequent.iter().copied() {
          seed_type_decls_from_stmt(
            state,
            body,
            child,
            binding_defs,
            seen_names,
            enclosing,
            in_enclosing_block,
          );
        }
      }
    }
    hir_js::StmtKind::Try {
      block,
      catch,
      finally_block,
    } => {
      seed_type_decls_from_stmt(
        state,
        body,
        *block,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
      if let Some(catch) = catch {
        seed_type_decls_from_stmt(
          state,
          body,
          catch.body,
          binding_defs,
          seen_names,
          enclosing,
          in_enclosing_block,
        );
      }
      if let Some(finally) = finally_block {
        seed_type_decls_from_stmt(
          state,
          body,
          *finally,
          binding_defs,
          seen_names,
          enclosing,
          in_enclosing_block,
        );
      }
    }
    hir_js::StmtKind::Labeled { body: inner, .. } | hir_js::StmtKind::With { body: inner, .. } => {
      seed_type_decls_from_stmt(
        state,
        body,
        *inner,
        binding_defs,
        seen_names,
        enclosing,
        in_enclosing_block,
      );
    }
    _ => {}
  }
}
