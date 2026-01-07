use super::*;

mod ambient;
mod decls;
mod lowering;
mod namespace;

impl ProgramState {
  pub(in super::super) fn bind_file(
    &mut self,
    file: FileId,
    ast: &Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) -> sem_ts::HirFile {
    let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
    let has_module_syntax = sem_ts::module_syntax::ast_has_module_syntax(ast);
    let mut sem_builder = SemHirBuilder::new(file, sem_file_kind(file_kind));
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut reexports = Vec::new();
    let mut export_all = Vec::new();

    for stmt in ast.stx.body.iter() {
      self.queue_type_imports_in_stmt(file, stmt, host, queue);
      match stmt.stx.as_ref() {
        Stmt::VarDecl(var) => {
          let new_defs = self.handle_var_decl(file, var.stx.as_ref(), &mut sem_builder);
          for (def_id, binding, export_name) in new_defs {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::FunctionDecl(func) => {
          let span = loc_to_span(file, stmt.loc);
          if let Some((def_id, binding, export_name)) =
            self.handle_function_decl(file, span.range, func.stx.as_ref(), &mut sem_builder)
          {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::InterfaceDecl(interface) => {
          let span = loc_to_span(file, stmt.loc);
          let name = interface.stx.name.clone();
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          let typ = self.store.primitive_ids().unknown;

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
          sem_builder.add_decl(
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

          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            },
          );

          if interface.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(typ),
              },
            );
          }

          self.record_symbol(file, span.range, symbol);
        }
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let name = alias.stx.name.clone();
          let ty = self.type_from_type_expr(&alias.stx.type_expr);
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
          sem_builder.add_decl(
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
          if alias.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(ty),
              },
            );
          }
        }
        Stmt::NamespaceDecl(ns) => {
          let span = loc_to_span(file, stmt.loc);
          let name = ns.stx.name.clone();
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: ns.stx.export,
              kind: DefKind::Namespace(NamespaceData {
                body: None,
                value_type: None,
                type_type: None,
                declare: ns.stx.declare,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          self.bind_namespace_member_defs(file, &ns.stx.body, sem_builder.file_kind, &mut defs);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if ns.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
        }
        Stmt::ModuleDecl(module) => {
          if let parse_js::ast::ts_stmt::ModuleName::String(specifier) = &module.stx.name {
            if has_module_syntax {
              // `declare module "x" { ... }` can act as an external module augmentation
              // when the containing file is itself a module. Record the host mapping
              // so `semantic-js` can resolve the augmentation target and merge it
              // into the module's exports.
              if let Some(target) = self.record_module_resolution(file, specifier, host) {
                queue.push_back(target);
              }
            }
            self.bind_ambient_module(file, module, &mut sem_builder, &mut defs);
          }
          let span = loc_to_span(file, stmt.loc);
          let name = match &module.stx.name {
            parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
            parse_js::ast::ts_stmt::ModuleName::String(s) => s.clone(),
          };
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: module.stx.export,
              kind: DefKind::Module(ModuleData {
                body: None,
                value_type: None,
                type_type: None,
                declare: module.stx.declare,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if module.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
        }
        Stmt::ExportDefaultExpr(node) => {
          let span = loc_to_span(file, node.loc);
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: "default".to_string(),
              file,
              span: span.range,
              symbol,
              export: true,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: MISSING_BODY,
                mode: VarDeclMode::Const,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          sem_builder.add_decl(
            def_id,
            "default".to_string(),
            sem_ts::DeclKind::Var,
            sem_ts::Exported::Default,
            span.range,
          );
          bindings.insert(
            "default".to_string(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          exports.insert(
            "default".to_string(),
            ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
        }
        Stmt::ExportList(export_list) => {
          let resolved = export_list
            .stx
            .from
            .as_ref()
            .and_then(|module| self.record_module_resolution(file, module, host));
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          match &export_list.stx.names {
            ExportNames::Specific(names) => {
              for name in names {
                let exportable = name.stx.exportable.as_str().to_string();
                let alias = name.stx.alias.stx.name.clone();
                let exported_as = if alias == exportable {
                  None
                } else {
                  Some(alias.clone())
                };
                let is_type_only = export_list.stx.type_only || name.stx.type_only;
                sem_builder.add_named_export(
                  export_list.stx.from.clone(),
                  export_list
                    .stx
                    .from
                    .as_ref()
                    .map(|_| loc_to_span(file, stmt.loc).range),
                  vec![sem_ts::ExportSpecifier {
                    local: exportable.clone(),
                    exported: exported_as.clone(),
                    local_span: loc_to_span(file, name.loc).range,
                    exported_span: exported_as
                      .as_ref()
                      .map(|_| loc_to_span(file, name.stx.alias.loc).range),
                  }],
                  is_type_only,
                );

                if let Some(target) = resolved {
                  reexports.push(Reexport {
                    from: target,
                    original: exportable.clone(),
                    alias: alias.clone(),
                    type_only: is_type_only,
                    span: loc_to_span(file, name.loc).range,
                  });
                }

                if export_list.stx.from.is_none() && !is_type_only {
                  let mapped = bindings.get(&exportable);
                  if let Some(binding) = mapped {
                    exports.insert(
                      alias.clone(),
                      ExportEntry {
                        symbol: binding.symbol,
                        def: binding.def,
                        type_id: binding.type_id,
                      },
                    );
                  } else {
                    self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                      format!("unknown export {exportable}"),
                      loc_to_span(file, name.loc),
                    ));
                  }
                }
              }
            }
            ExportNames::All(alias) => {
              if let Some(spec) = export_list.stx.from.clone() {
                if alias.is_none() {
                  if let Some(target) = resolved {
                    export_all.push(ExportAll {
                      from: target,
                      type_only: export_list.stx.type_only,
                    });
                  }
                }
                let alias = alias
                  .as_ref()
                  .map(|alias| (alias.stx.name.clone(), loc_to_span(file, alias.loc).range));
                sem_builder.add_export_all(
                  spec,
                  loc_to_span(file, stmt.loc).range,
                  export_list.stx.type_only,
                  alias,
                );
              }
            }
          }
        }
        Stmt::Import(import_stmt) => {
          let module = import_stmt.stx.module.clone();
          let resolved = self.record_module_resolution(file, &module, host);
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          let import_target =
            resolved
              .map(ImportTarget::File)
              .unwrap_or_else(|| ImportTarget::Unresolved {
                specifier: module.clone(),
              });
          let mut import_default = None;
          let mut import_namespace = None;
          let mut import_named = Vec::new();
          if let Some(default_pat) = import_stmt.stx.default.as_ref() {
            let alias_name = match &default_pat.stx.pat.stx.as_ref() {
              Pat::Id(id) => id.stx.name.clone(),
              _ => {
                self
                  .diagnostics
                  .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                    "unsupported import pattern",
                    loc_to_span(file, default_pat.loc),
                  ));
                continue;
              }
            };
            import_default = Some(sem_ts::ImportDefault {
              local: alias_name.clone(),
              local_span: loc_to_span(file, default_pat.loc).range,
              is_type_only: import_stmt.stx.type_only,
            });
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: alias_name.clone(),
                file,
                span: loc_to_span(file, default_pat.loc).range,
                symbol,
                export: false,
                kind: DefKind::Import(ImportData {
                  target: import_target.clone(),
                  original: "default".to_string(),
                }),
              },
            );
            defs.push(def_id);
            bindings.insert(
              alias_name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, loc_to_span(file, default_pat.loc).range, symbol);
          }
          match import_stmt.stx.names {
            Some(ImportNames::Specific(ref list)) => {
              for entry in list {
                let name = entry.stx.importable.as_str().to_string();
                let alias_pat = &entry.stx.alias;
                let alias_name = match &alias_pat.stx.pat.stx.as_ref() {
                  Pat::Id(id) => id.stx.name.clone(),
                  _ => {
                    self
                      .diagnostics
                      .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                        "unsupported import pattern",
                        loc_to_span(file, alias_pat.loc),
                      ));
                    continue;
                  }
                };
                let is_type_only = import_stmt.stx.type_only || entry.stx.type_only;
                import_named.push(sem_ts::ImportNamed {
                  imported: name.clone(),
                  local: alias_name.clone(),
                  is_type_only,
                  imported_span: loc_to_span(file, entry.loc).range,
                  local_span: loc_to_span(file, alias_pat.loc).range,
                });
                let symbol = self.alloc_symbol();
                let def_id = self.alloc_def();
                self.def_data.insert(
                  def_id,
                  DefData {
                    name: alias_name.clone(),
                    file,
                    span: loc_to_span(file, alias_pat.loc).range,
                    symbol,
                    export: false,
                    kind: DefKind::Import(ImportData {
                      target: import_target.clone(),
                      original: name.clone(),
                    }),
                  },
                );
                self.record_def_symbol(def_id, symbol);
                defs.push(def_id);
                bindings.insert(
                  alias_name.clone(),
                  SymbolBinding {
                    symbol,
                    def: Some(def_id),
                    type_id: None,
                  },
                );
                self.record_symbol(file, loc_to_span(file, alias_pat.loc).range, symbol);
              }
            }
            Some(ImportNames::All(ref pat)) => {
              let alias_name = match &pat.stx.pat.stx.as_ref() {
                Pat::Id(id) => id.stx.name.clone(),
                _ => {
                  self.diagnostics.push(
                    codes::UNSUPPORTED_IMPORT_PATTERN
                      .error("unsupported import pattern", loc_to_span(file, pat.loc)),
                  );
                  continue;
                }
              };
              import_namespace = Some(sem_ts::ImportNamespace {
                local: alias_name.clone(),
                local_span: loc_to_span(file, pat.loc).range,
                is_type_only: import_stmt.stx.type_only,
              });
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: alias_name.clone(),
                  file,
                  span: loc_to_span(file, pat.loc).range,
                  symbol,
                  export: false,
                  kind: DefKind::Import(ImportData {
                    target: import_target.clone(),
                    original: "*".to_string(),
                  }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              bindings.insert(
                alias_name.clone(),
                SymbolBinding {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
              self.record_symbol(file, loc_to_span(file, pat.loc).range, symbol);
            }
            None => {}
          }
          sem_builder.add_import(sem_ts::Import {
            specifier: module,
            specifier_span: loc_to_span(file, stmt.loc).range,
            default: import_default,
            namespace: import_namespace,
            named: import_named,
            is_type_only: import_stmt.stx.type_only,
          });
        }
        Stmt::ImportEqualsDecl(import_equals) => match &import_equals.stx.rhs {
          ImportEqualsRhs::Require { module } => {
            let resolved = self.record_module_resolution(file, module, host);
            if let Some(target) = resolved {
              queue.push_back(target);
            }
            let import_target =
              resolved
                .map(ImportTarget::File)
                .unwrap_or_else(|| ImportTarget::Unresolved {
                  specifier: module.clone(),
                });
            let span = loc_to_span(file, stmt.loc).range;
            self
              .import_assignment_requires
              .push(ImportAssignmentRequireRecord {
                file,
                span,
                target: import_target.clone(),
              });
            let name = import_equals.stx.name.clone();
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span,
                symbol,
                export: import_equals.stx.export,
                kind: DefKind::Import(ImportData {
                  target: import_target.clone(),
                  original: "*".to_string(),
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
                type_id: None,
              },
            );
            self.record_symbol(file, span, symbol);
            if import_equals.stx.export {
              exports.insert(
                name.clone(),
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
            }
            sem_builder.add_import_equals(sem_ts::ImportEquals {
              local: name,
              local_span: span,
              target: sem_ts::ImportEqualsTarget::Require {
                specifier: module.clone(),
                specifier_span: span,
              },
              is_exported: import_equals.stx.export,
            });
          }
          ImportEqualsRhs::EntityName { path } => {
            let span = loc_to_span(file, stmt.loc).range;
            let name = import_equals.stx.name.clone();
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span,
                symbol,
                export: import_equals.stx.export,
                kind: DefKind::ImportAlias(ImportAliasData { path: path.clone() }),
              },
            );
            self.record_def_symbol(def_id, symbol);
            defs.push(def_id);
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, span, symbol);
            if import_equals.stx.export {
              exports.insert(
                name.clone(),
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
            }
            sem_builder.add_import_equals(sem_ts::ImportEquals {
              local: name,
              local_span: span,
              target: sem_ts::ImportEqualsTarget::EntityName {
                path: path.clone(),
                span,
              },
              is_exported: import_equals.stx.export,
            });
          }
        },
        Stmt::Expr(_) | Stmt::If(_) | Stmt::Block(_) | Stmt::While(_) => {}
        _ => {}
      }
    }

    self.files.insert(
      file,
      FileState {
        defs,
        exports,
        bindings,
        top_body: None,
        reexports,
        export_all,
      },
    );
    sem_builder.finish()
  }
}
