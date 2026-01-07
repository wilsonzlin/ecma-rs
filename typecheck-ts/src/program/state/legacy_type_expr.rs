use super::*;

impl ProgramState {
  pub(super) fn object_type_from_members(&mut self, members: &[Node<TypeMember>]) -> ObjectType {
    let mut object = ObjectType::empty();
    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some(name) = type_member_name(&prop.stx.key) {
            let ty = prop
              .stx
              .type_annotation
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
              .unwrap_or(self.builtin.unknown);
            object.props.insert(
              name,
              ObjectProperty {
                typ: ty,
                optional: prop.stx.optional,
                readonly: prop.stx.readonly,
              },
            );
          }
        }
        TypeMember::Method(method) => {
          if let Some(name) = type_member_name(&method.stx.key) {
            let params = method
              .stx
              .parameters
              .iter()
              .map(|p| self.type_from_type_expr(&p.stx.type_expr))
              .collect();
            let ret = method
              .stx
              .return_type
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
              .unwrap_or(self.builtin.unknown);
            let func_ty = self.type_store.function(params, ret);
            object.props.insert(
              name,
              ObjectProperty {
                typ: func_ty,
                optional: method.stx.optional,
                readonly: false,
              },
            );
          }
        }
        TypeMember::IndexSignature(index) => {
          let value = self.type_from_type_expr(&index.stx.type_annotation);
          let param_type = self.type_from_type_expr(&index.stx.parameter_type);
          let param_kind = self.type_store.kind(param_type).clone();
          match param_kind {
            TypeKind::Number => object.number_index = Some(value),
            TypeKind::String => object.string_index = Some(value),
            _ => object.string_index = Some(value),
          }
        }
        _ => {}
      }
    }
    object
  }

  pub(super) fn merge_object_types(&mut self, mut base: ObjectType, extra: ObjectType) -> ObjectType {
    for (name, prop) in extra.props.into_iter() {
      match base.props.entry(name) {
        Entry::Vacant(entry) => {
          entry.insert(prop);
        }
        Entry::Occupied(mut entry) => {
          let existing = entry.get_mut();
          existing.typ = self
            .type_store
            .union(vec![existing.typ, prop.typ], &self.builtin);
          existing.optional = existing.optional || prop.optional;
          existing.readonly = existing.readonly || prop.readonly;
        }
      }
    }

    if base.string_index.is_none() {
      base.string_index = extra.string_index;
    }
    if base.number_index.is_none() {
      base.number_index = extra.number_index;
    }

    base
  }

  pub(super) fn type_from_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
      TypeExpr::TypeReference(reference) => {
        if let Some(file) = self.current_file {
          let span = loc_to_span(file, reference.loc).range;
          let mut segments = Vec::new();
          fn collect_segments(name: &TypeEntityName, out: &mut Vec<String>) {
            match name {
              TypeEntityName::Identifier(id) => out.push(id.clone()),
              TypeEntityName::Qualified(qn) => {
                collect_segments(&qn.left, out);
                out.push(qn.right.clone());
              }
              TypeEntityName::Import(_) => {}
            }
          }
          collect_segments(&reference.stx.name, &mut segments);
          let mut binding_defs = HashMap::new();
          if let Some(state) = self.files.get(&file) {
            for (name, binding) in state.bindings.iter() {
              if let Some(def) = binding.def {
                binding_defs.insert(name.clone(), def);
              }
            }
          }

          let mut resolved_def = None;
          if !binding_defs.is_empty() {
            if let Some(resolver) = self.build_type_resolver(&binding_defs) {
              resolved_def = resolver.resolve_type_name(&segments);
            }
          }

          if resolved_def.is_none() {
            if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
              let mut entries: Vec<_> = self.def_data.iter().collect();
              entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
              let mut best: Option<(DefId, u8)> = None;
              for (id, data) in entries.into_iter() {
                if data.name != *type_name {
                  continue;
                }
                let pri = self.def_priority(*id, sem_ts::Namespace::TYPE);
                match best {
                  Some((_, existing)) if existing <= pri => {}
                  _ => best = Some((*id, pri)),
                }
              }
              if let Some((id, _)) = best {
                resolved_def = Some(id);
              }
            }
          }

          if let Some(def) = resolved_def {
            if let Some(symbol) = self.def_data.get(&def).map(|d| d.symbol) {
              self.record_symbol(file, span, symbol);
            }
            if let Err(fatal) = self.type_of_def(def) {
              if !matches!(fatal, FatalError::Cancelled) {
                self.diagnostics.push(fatal_to_diagnostic(fatal));
              }
              return self.builtin.unknown;
            }
            if let Some(store) = self.interned_store.as_ref() {
              if let Some(ty) = self.interned_def_types.get(&def).copied() {
                let ty = store.canon(ty);
                if !matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
                  return ty;
                }
              }
            }
            return self
              .def_types
              .get(&def)
              .copied()
              .unwrap_or(self.builtin.unknown);
          }
        }
        self.builtin.unknown
      }
      TypeExpr::Object(_) => self.builtin.object,
      TypeExpr::Number(_) => self.builtin.number,
      TypeExpr::String(_) => self.builtin.string,
      TypeExpr::Boolean(_) => self.builtin.boolean,
      TypeExpr::Any(_) => self.builtin.any,
      TypeExpr::Unknown(_) => self.builtin.unknown,
      TypeExpr::Null(_) => self.builtin.null,
      TypeExpr::Undefined(_) => self.builtin.undefined,
      TypeExpr::Void(_) => self.builtin.void,
      TypeExpr::Never(_) => self.builtin.never,
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.type_from_type_expr(t)).collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeExpr::TupleType(tuple) => {
        let readonly = tuple.stx.readonly;
        let elements = tuple
          .stx
          .elements
          .iter()
          .map(|elem| self.type_from_type_expr(&elem.stx.type_expr))
          .collect();
        self.type_store.tuple(elements, readonly)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(element_type);
        self.type_store.array(elem)
      }
      TypeExpr::FunctionType(func) => {
        let params = func
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&func.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ConstructorType(cons) => {
        let params = cons
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&cons.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ObjectType(obj) => {
        let object = self.object_type_from_members(&obj.stx.members);
        self.type_store.object(object)
      }
      TypeExpr::MappedType(mapped) => {
        let source = self.type_from_type_expr(&mapped.stx.constraint);
        let value = self.type_from_type_expr(&mapped.stx.type_expr);
        self.type_store.mapped(source, value)
      }
      TypeExpr::ParenthesizedType(inner) => self.type_from_type_expr(&inner.stx.type_expr),
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::Boolean(value) => self.type_store.literal_boolean(*value),
        TypeLiteral::Number(n) => self.type_store.literal_number(n.clone()),
        TypeLiteral::String(s) => self.type_store.literal_string(s.clone()),
        TypeLiteral::Null => self.builtin.null,
        _ => self.builtin.unknown,
      },
      TypeExpr::TypePredicate(pred) => {
        let asserted = pred
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t));
        self
          .type_store
          .predicate(pred.stx.parameter_name.clone(), asserted, pred.stx.asserts)
      }
      TypeExpr::TypeQuery(query) => {
        fn entity_name_segments(name: &TypeEntityName) -> Option<Vec<String>> {
          match name {
            TypeEntityName::Identifier(id) => Some(vec![id.clone()]),
            TypeEntityName::Qualified(qualified) => {
              let mut parts = entity_name_segments(&qualified.left)?;
              parts.push(qualified.right.clone());
              Some(parts)
            }
            TypeEntityName::Import(_) => None,
          }
        }

        if let Some(path) = entity_name_segments(&query.stx.expr_name) {
          let mut binding_defs = HashMap::new();
          let mut local_binding = None;
          if let Some(file) = self.current_file {
            if let Some(state) = self.files.get(&file) {
              for (name, binding) in state.bindings.iter() {
                if let Some(def) = binding.def {
                  binding_defs.insert(name.clone(), def);
                }
              }
              if path.len() == 1 {
                local_binding = state.bindings.get(&path[0]).cloned();
              }
            }
          }
          if let Some(binding) = local_binding {
            if let Some(file) = self.current_file {
              self.record_symbol(file, loc_to_span(file, query.loc).range, binding.symbol);
            }
            let mut ty = None;
            if let Some(def) = binding.def {
              if let Some(DefKind::Import(import)) = self.def_data.get(&def).map(|d| d.kind.clone())
              {
                if let Ok(exports) = self.exports_for_import(&import) {
                  if let Some(entry) = exports.get(&import.original) {
                    let mut mapped = None;
                    if let Some(target_def) = entry.def {
                      if let Ok(Some(exported)) = self.export_type_for_def(target_def) {
                        mapped = Some(exported);
                      } else if let Ok(found) = self.type_of_def(target_def) {
                        mapped = Some(found);
                      }
                    }
                    if mapped.is_none() {
                      mapped = entry.type_id;
                    }
                    if let Some(mapped) = mapped {
                      let mapped = match self.resolve_value_ref_type(mapped) {
                        Ok(resolved) => resolved,
                        Err(FatalError::Cancelled) => return self.builtin.unknown,
                        Err(fatal) => {
                          self.diagnostics.push(fatal_to_diagnostic(fatal));
                          self.builtin.unknown
                        }
                      };
                      if mapped != self.builtin.unknown {
                        return mapped;
                      }
                    }
                  }
                }
              }
              match self.type_of_def(def) {
                Ok(found) => ty = Some(found),
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  return self.builtin.unknown;
                }
              }
            }
            if ty.is_none() {
              ty = binding.type_id;
            }
            if let Some(ty) = ty {
              let ty = match self.resolve_value_ref_type(ty) {
                Ok(resolved) => resolved,
                Err(FatalError::Cancelled) => return self.builtin.unknown,
                Err(fatal) => {
                  self.diagnostics.push(fatal_to_diagnostic(fatal));
                  self.builtin.unknown
                }
              };
              if ty != self.builtin.unknown {
                return ty;
              }
            }
          }
          if let Some(resolver) = self.build_type_resolver(&binding_defs) {
            if let Some(def) = resolver.resolve_typeof(&path) {
              return match self.type_of_def(def) {
                Ok(ty) => match self.resolve_value_ref_type(ty) {
                  Ok(resolved) => resolved,
                  Err(FatalError::Cancelled) => self.builtin.unknown,
                  Err(fatal) => {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                    self.builtin.unknown
                  }
                },
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  self.builtin.unknown
                }
              };
            }
          }
          if path.len() == 1 {
            let mut entries: Vec<_> = self.def_data.iter().collect();
            entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
            let mut best: Option<(DefId, u8)> = None;
            for (id, data) in entries.into_iter() {
              if data.name != path[0] {
                continue;
              }
              let pri = self.def_priority(*id, sem_ts::Namespace::VALUE);
              match best {
                Some((_, existing)) if existing <= pri => {}
                _ => best = Some((*id, pri)),
              }
            }
            if let Some((id, _)) = best {
              return match self.type_of_def(id) {
                Ok(ty) => match self.resolve_value_ref_type(ty) {
                  Ok(resolved) => resolved,
                  Err(FatalError::Cancelled) => self.builtin.unknown,
                  Err(fatal) => {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                    self.builtin.unknown
                  }
                },
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  self.builtin.unknown
                }
              };
            }
          }
        }

        self.builtin.unknown
      }
      _ => self.builtin.unknown,
    }
  }

}
