use super::*;

impl ProgramState {
  pub(super) fn bind_ambient_module(
    &mut self,
    file: FileId,
    module: &Node<parse_js::ast::ts_stmt::ModuleDecl>,
    builder: &mut SemHirBuilder,
    defs: &mut Vec<DefId>,
  ) {
    let Some(body) = module.stx.body.as_ref() else {
      return;
    };
    let name_span = loc_to_span(file, module.loc).range;
    let name = match &module.stx.name {
      parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
      parse_js::ast::ts_stmt::ModuleName::String(specifier) => specifier.clone(),
    };
    let mut module_builder = SemHirBuilder::new_ambient(file, builder.file_kind);
    let mut bindings = HashMap::new();
    for stmt in body.iter() {
      self.bind_ambient_stmt(file, stmt, &mut module_builder, &mut bindings, defs);
    }
    builder.add_ambient_module(module_builder.into_ambient(name, name_span));
  }

  pub(super) fn bind_ambient_stmt(
    &mut self,
    file: FileId,
    stmt: &Node<Stmt>,
    builder: &mut SemHirBuilder,
    bindings: &mut HashMap<String, SymbolBinding>,
    defs: &mut Vec<DefId>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::AmbientVarDecl(var) => {
        let span = loc_to_span(file, stmt.loc);
        let name = var.stx.name.clone();
        let typ = var
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t));
        let symbol = self.alloc_symbol();
        let def_id = self.alloc_def();
        self.record_symbol(file, span.range, symbol);
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: span.range,
            symbol,
            export: var.stx.export,
            kind: DefKind::Var(VarData {
              typ,
              init: None,
              body: MISSING_BODY,
              mode: VarDeclMode::Var,
            }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        defs.push(def_id);
        bindings.insert(
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: typ,
          },
        );
        builder.add_decl(
          def_id,
          name,
          sem_ts::DeclKind::Var,
          if var.stx.export {
            sem_ts::Exported::Named
          } else {
            sem_ts::Exported::No
          },
          span.range,
        );
      }
      Stmt::VarDecl(var) => {
        let new_defs = self.handle_var_decl(file, var.stx.as_ref(), builder);
        for (def_id, binding, _export_name) in new_defs {
          defs.push(def_id);
          let (name, value) = binding;
          bindings.insert(name, value);
        }
      }
      Stmt::FunctionDecl(func) => {
        let span = loc_to_span(file, stmt.loc);
        if let Some((def_id, binding, _export_name)) =
          self.handle_function_decl(file, span.range, func.stx.as_ref(), builder)
        {
          defs.push(def_id);
          let (name, value) = binding;
          bindings.insert(name, value);
        }
      }
      Stmt::InterfaceDecl(interface) => {
        let span = loc_to_span(file, stmt.loc);
        let name = interface.stx.name.clone();
        let mut object = self.object_type_from_members(&interface.stx.members);
        for base in interface.stx.extends.iter() {
          let base_ty = self.type_from_type_expr(base);
          if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
            object = self.merge_object_types(object, base_obj);
          }
        }
        let mut typ = self.type_store.object(object);
        let existing_interface = bindings
          .get(&name)
          .and_then(|b| b.def)
          .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
          .and_then(|(id, data)| match data.kind {
            DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
            _ => None,
          });
        let (def_id, symbol) = if let Some((existing_id, symbol, existing_ty)) = existing_interface
        {
          typ = match (
            self.type_store.kind(existing_ty).clone(),
            self.type_store.kind(typ).clone(),
          ) {
            (TypeKind::Object(existing_obj), TypeKind::Object(obj)) => {
              let merged = self.merge_object_types(existing_obj, obj);
              self.type_store.object(merged)
            }
            _ => self.type_store.union(vec![existing_ty, typ], &self.builtin),
          };
          if let Some(def) = self.def_data.get_mut(&existing_id) {
            def.kind = DefKind::Interface(InterfaceData { typ });
            def.export = def.export || interface.stx.export;
          }
          (existing_id, symbol)
        } else {
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: interface.stx.export,
              kind: DefKind::Interface(InterfaceData { typ }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          builder.add_decl(
            def_id,
            name.clone(),
            sem_ts::DeclKind::Interface,
            if interface.stx.export {
              sem_ts::Exported::Named
            } else {
              sem_ts::Exported::No
            },
            span.range,
          );
          (def_id, symbol)
        };

        bindings
          .entry(name.clone())
          .and_modify(|binding| {
            binding.symbol = symbol;
            binding.def = Some(def_id);
            binding.type_id = Some(typ);
          })
          .or_insert(SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: Some(typ),
          });

        self.def_types.insert(def_id, typ);
        self.record_symbol(file, span.range, symbol);
      }
      Stmt::TypeAliasDecl(alias) => {
        let span = loc_to_span(file, stmt.loc);
        let name = alias.stx.name.clone();
        let mut ty = self.type_from_type_expr(&alias.stx.type_expr);
        if ty == self.builtin.unknown {
          ty = self.type_store.literal_string(name.clone());
        }
        if let TypeExpr::TypeReference(reference) = alias.stx.type_expr.stx.as_ref() {
          if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
            if let Some(binding) = bindings.get(type_name) {
              self.record_symbol(
                file,
                loc_to_span(file, alias.stx.type_expr.loc).range,
                binding.symbol,
              );
            }
          }
        }
        let def_id = self.alloc_def();
        let symbol = self.alloc_symbol();
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: span.range,
            symbol,
            export: alias.stx.export,
            kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        self.def_types.insert(def_id, ty);
        bindings.insert(
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: Some(ty),
          },
        );
        defs.push(def_id);
        self.record_symbol(file, span.range, symbol);
        builder.add_decl(
          def_id,
          name.clone(),
          sem_ts::DeclKind::TypeAlias,
          if alias.stx.export {
            sem_ts::Exported::Named
          } else {
            sem_ts::Exported::No
          },
          span.range,
        );
      }
      Stmt::NamespaceDecl(ns) => {
        self.bind_ambient_namespace_body(file, &ns.stx.body, builder, bindings, defs);
      }
      Stmt::ModuleDecl(module) => {
        if matches!(
          module.stx.name,
          parse_js::ast::ts_stmt::ModuleName::String(_)
        ) {
          self.bind_ambient_module(file, module, builder, defs);
        }
      }
      _ => {}
    }
  }

  pub(super) fn bind_ambient_namespace_body(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    builder: &mut SemHirBuilder,
    bindings: &mut HashMap<String, SymbolBinding>,
    defs: &mut Vec<DefId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => {
        for stmt in stmts.iter() {
          self.bind_ambient_stmt(file, stmt, builder, bindings, defs);
        }
      }
      NamespaceBody::Namespace(inner) => {
        self.bind_ambient_namespace_body(file, &inner.stx.body, builder, bindings, defs)
      }
    }
  }

}
