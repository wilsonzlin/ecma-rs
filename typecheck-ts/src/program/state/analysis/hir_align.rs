use super::*;

impl ProgramState {
  /// Remap bound definitions to the stable IDs produced by HIR lowering while
  /// preserving existing symbols and cached types.
  ///
  /// The binder allocates definitions sequentially, but HIR uses content-derived
  /// identifiers that stay stable across edits. Re-aligning keeps
  /// `definitions_in_file`, `expr_at`, and `type_of_def` working across repeated
  /// checks and avoids dropping cached type information when files are
  /// re-lowered.
  pub(super) fn align_definitions_with_hir(
    &mut self,
    file: FileId,
    lowered: &LowerResult,
  ) -> HashMap<DefId, DefId> {
    let is_file_level_binding = |def: &hir_js::DefData| -> bool {
      if def.in_global {
        // `declare global { ... }` members are injected into the program-wide
        // global scope but do not create file/module bindings.
        return false;
      }

      // `hir-js` models variable declarations as a `VarDeclarator` container
      // owning the initializer body plus one or more `Var` children for the
      // bindings. Treat those `Var` defs as top-level when the declarator
      // itself is top-level.
      let mut parent = def.parent;
      while let Some(parent_id) = parent {
        let Some(parent_def) = lowered.def(parent_id) else {
          return false;
        };
        if matches!(parent_def.path.kind, HirDefKind::VarDeclarator) {
          parent = parent_def.parent;
          continue;
        }
        return false;
      }

      matches!(
        def.path.kind,
        HirDefKind::Var
          | HirDefKind::Function
          | HirDefKind::Class
          | HirDefKind::Enum
          | HirDefKind::Namespace
          | HirDefKind::Module
          | HirDefKind::ImportBinding
          | HirDefKind::Interface
          | HirDefKind::TypeAlias
          | HirDefKind::ExportAlias
      )
    };

    let file_def_ids: HashSet<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .map(|(id, _)| *id)
      .collect();
    let mut by_name_kind: HashMap<(String, DefMatchKind), Vec<(DefId, DefData)>> = HashMap::new();
    for (id, data) in self.def_data.iter() {
      if data.file != file {
        continue;
      }
      by_name_kind
        .entry((data.name.clone(), match_kind_from_def(&data.kind)))
        .or_default()
        .push((*id, data.clone()));
    }
    for defs in by_name_kind.values_mut() {
      defs.sort_by_key(|(_, data)| (data.span.start, data.span.end));
    }

    let mut new_def_data: HashMap<DefId, DefData> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file != file)
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    let mut new_def_types: HashMap<DefId, TypeId> = self
      .def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_def_types: HashMap<DefId, tti::TypeId> = self
      .interned_def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_type_params: HashMap<DefId, Vec<TypeParamId>> = self
      .interned_type_params
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, params)| (*id, params.clone()))
      .collect();
    let mut new_interned_type_param_decls: HashMap<DefId, Arc<[tti::TypeParamDecl]>> = self
      .interned_type_param_decls
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, decls)| (*id, Arc::clone(decls)))
      .collect();
    let mut id_mapping: HashMap<DefId, DefId> = HashMap::new();

    let Some(file_state) = self.files.get(&file).cloned() else {
      return HashMap::new();
    };
    let mut resolved_defs = Vec::new();
    let mut bindings = file_state.bindings.clone();
    let mut exports = file_state.exports.clone();
    let reexports = file_state.reexports.clone();
    let export_all = file_state.export_all.clone();

    // `hir-js` definition order is not guaranteed to match source order (IDs
    // are content-derived). Align by spans to keep stable IDs wired to the
    // correct bound declaration when multiple defs share a name (e.g. globals
    // vs ambient modules).
    let mut lowered_defs: Vec<_> = lowered.defs.iter().collect();
    lowered_defs.sort_by_key(|def| (def.span.start, def.span.end, def.id.0));
    for def in lowered_defs {
      let raw_name = lowered
        .names
        .resolve(def.name)
        .unwrap_or_default()
        .to_string();
      // `hir-js` emits `VarDeclarator` defs as a container for the declaration
      // itself, alongside `Var` defs for the bound identifiers. Keep the
      // declarator defs addressable by ID, but avoid treating them as the named
      // binding to keep `definitions_in_file` name-based queries focused on
      // actual bindings.
      let is_var_declarator = def.path.kind == HirDefKind::VarDeclarator;
      let name = if is_var_declarator {
        format!("<var_decl:{raw_name}>")
      } else {
        raw_name.clone()
      };
      let match_kind = match_kind_from_hir(def.path.kind);
      // `hir-js` models variable declarations as a `VarDeclarator` node that owns the initializer
      // body plus one or more child `Var` defs for the bindings (to support destructuring).
      //
      // Track `VarDeclarator` as a definition for stable IDs, but do not treat it as a symbol in
      // any namespace or allow it to clobber the real `Var` binding in `bindings`/`exports`.
      let is_var_declarator = matches!(match_kind, DefMatchKind::VarDeclarator);
      let matched = by_name_kind
        .get_mut(&(name.clone(), match_kind))
        .and_then(|list| {
          if list.is_empty() {
            None
          } else {
            Some(list.remove(0))
          }
        });
      let (def_id, data) = if let Some((old_id, mut data)) = matched {
        id_mapping.insert(old_id, def.id);
        data.span = def.span;
        data.export = data.export || def.is_exported || def.is_default_export;
        if is_var_declarator {
          data.export = false;
        }
        match &mut data.kind {
          DefKind::Function(func) => func.body = def.body,
          DefKind::Var(var) => {
            if let Some(body) = def.body {
              var.body = body;
            }
          }
          DefKind::VarDeclarator(var) => {
            var.body = def.body;
          }
          DefKind::Class(class) => {
            class.body = def.body;
            class.declare |= def.is_ambient;
          }
          DefKind::Enum(en) => {
            en.body = def.body;
            en.declare |= def.is_ambient;
          }
          DefKind::Namespace(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          DefKind::Module(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          _ => {}
        }
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(def.id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(def.id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(def.id, params);
        }
        if let Some(decls) = self.interned_type_param_decls.get(&old_id).cloned() {
          new_interned_type_param_decls.insert(def.id, decls);
        }
        (def.id, data)
      } else {
        let symbol = self.alloc_symbol();
        let kind = match match_kind {
          DefMatchKind::Function => DefKind::Function(FuncData {
            params: def
              .body
              .and_then(|body_id| lowered.body(body_id))
              .and_then(|body| body.function.as_ref().map(|func| (body, func)))
              .map(|(body, func)| {
                func
                  .params
                  .iter()
                  .enumerate()
                  .map(|(index, param)| {
                    let name = match body.pats.get(param.pat.0 as usize).map(|pat| &pat.kind) {
                      Some(HirPatKind::Ident(name_id)) => lowered
                        .names
                        .resolve(*name_id)
                        .unwrap_or_default()
                        .to_string(),
                      _ => format!("<pattern{index}>"),
                    };
                    ParamData {
                      name,
                      typ: None,
                      symbol: self.alloc_symbol(),
                      pat: None,
                    }
                  })
                  .collect()
              })
              .unwrap_or_default(),
            return_ann: None,
            body: def.body,
          }),
          DefMatchKind::VarDeclarator => {
            DefKind::VarDeclarator(VarDeclaratorData { body: def.body })
          }
          DefMatchKind::Class => DefKind::Class(ClassData {
            body: def.body,
            instance_type: None,
            static_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Enum => DefKind::Enum(EnumData {
            body: def.body,
            is_const: false,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Namespace => DefKind::Namespace(NamespaceData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Module => DefKind::Module(ModuleData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Interface => DefKind::Interface(InterfaceData {
            typ: self.builtin.unknown,
          }),
          DefMatchKind::TypeAlias => DefKind::TypeAlias(TypeAliasData {
            typ: self.builtin.unknown,
          }),
          _ => DefKind::Var(VarData {
            typ: None,
            init: None,
            body: def.body.unwrap_or(MISSING_BODY),
            mode: VarDeclMode::Var,
          }),
        };
        let export = if is_var_declarator {
          false
        } else {
          def.is_exported || def.is_default_export
        };
        let data = DefData {
          name: name.clone(),
          file,
          span: def.span,
          symbol,
          export,
          kind,
        };
        self.record_def_symbol(def.id, symbol);
        if !is_var_declarator {
          self.record_symbol(file, def.span, symbol);
        }
        (def.id, data)
      };

      if !is_var_declarator {
        if is_file_level_binding(def) {
          bindings
            .entry(raw_name.clone())
            .and_modify(|binding| {
              binding.symbol = data.symbol;
              binding.def = Some(def_id);
            })
            .or_insert(SymbolBinding {
              symbol: data.symbol,
              def: Some(def_id),
              type_id: None,
            });
        }
      }

      if data.export && !is_var_declarator && is_file_level_binding(def) {
        let export_name = if def.is_default_export {
          "default".to_string()
        } else {
          raw_name.clone()
        };
        exports.insert(
          export_name,
          ExportEntry {
            symbol: data.symbol,
            def: Some(def_id),
            type_id: new_def_types.get(&def_id).copied(),
          },
        );
      }

      new_def_data.insert(def_id, data);
      resolved_defs.push(def_id);
    }

    for leftovers in by_name_kind.values_mut() {
      for (old_id, data) in leftovers.drain(..) {
        new_def_data.insert(old_id, data.clone());
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(old_id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(old_id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(old_id, params);
        }
        if let Some(decls) = self.interned_type_param_decls.get(&old_id).cloned() {
          new_interned_type_param_decls.insert(old_id, decls);
        }
      }
    }

    for binding in bindings.values_mut() {
      if let Some(def) = binding.def {
        if let Some(mapped) = id_mapping.get(&def) {
          binding.def = Some(*mapped);
        }
      }
    }
    for entry in exports.values_mut() {
      if let Some(def) = entry.def {
        if let Some(mapped) = id_mapping.get(&def) {
          entry.def = Some(*mapped);
        }
      }
    }

    // Synthesize value-side definitions for classes/enums so `typeof` can map to a
    // dedicated value def without conflating with the instance/type-side def.
    // These defs are stable across runs: they are derived from the type-side `DefId`.
    self.value_defs.retain(|type_def, value_def| {
      !file_def_ids.contains(type_def) && !file_def_ids.contains(value_def)
    });
    let mut taken_ids: HashSet<DefId> = new_def_data.keys().copied().collect();
    let mut class_enum_type_defs: Vec<DefId> = Vec::new();
    for def_id in resolved_defs.iter().copied() {
      if let Some(data) = new_def_data.get(&def_id) {
        if matches!(data.kind, DefKind::Class(_) | DefKind::Enum(_)) {
          class_enum_type_defs.push(def_id);
        }
      }
    }
    class_enum_type_defs.sort_by_key(|d| d.0);
    for type_def in class_enum_type_defs {
      let Some(type_data) = new_def_data.get(&type_def).cloned() else {
        continue;
      };
      let tag = match type_data.kind {
        DefKind::Class(_) => 1u32,
        DefKind::Enum(_) => 2u32,
        _ => continue,
      };
      let value_def = alloc_synthetic_def_id(
        file,
        &mut taken_ids,
        &("ts_value_def", file.0, type_def.0, tag),
      );
      self.value_defs.insert(type_def, value_def);
      new_def_data.entry(value_def).or_insert_with(|| DefData {
        name: type_data.name.clone(),
        file: type_data.file,
        span: type_data.span,
        symbol: type_data.symbol,
        export: type_data.export,
        kind: DefKind::Var(VarData {
          typ: None,
          init: None,
          body: MISSING_BODY,
          mode: VarDeclMode::Let,
        }),
      });
      if let Some(binding) = bindings.get_mut(&type_data.name) {
        if binding.def == Some(type_def) {
          binding.def = Some(value_def);
        }
      }
      for entry in exports.values_mut() {
        if entry.def == Some(type_def) {
          entry.def = Some(value_def);
        }
      }
    }

    self.files.insert(
      file,
      FileState {
        defs: resolved_defs,
        exports,
        bindings,
        top_body: file_state.top_body,
        reexports,
        export_all,
      },
    );

    self.def_data = new_def_data;
    self.def_types = new_def_types;
    self.interned_def_types = new_interned_def_types;
    self.interned_type_params = new_interned_type_params;
    self.interned_type_param_decls = new_interned_type_param_decls;

    self.symbol_to_def.clear();
    for (def, data) in self.def_data.iter() {
      self.symbol_to_def.insert(data.symbol, *def);
    }
    self.next_def = self
      .def_data
      .keys()
      .map(|d| d.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);

    id_mapping
  }

  pub(super) fn map_hir_bodies(&mut self, file: FileId, lowered: &LowerResult) {
    // Bodies are keyed by stable hash-based IDs. In the (rare) event that a body id collides
    // across files, we must ensure we clear any stale metadata/parent edges before inserting the
    // newly-lowered bodies for `file`.
    let mut stale: HashSet<BodyId> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    stale.extend(lowered.body_index.keys().copied());
    self.body_map.retain(|id, _| !stale.contains(id));
    self.body_parents.retain(|child, _| !stale.contains(child));

    if let Some(state) = self.files.get_mut(&file) {
      state.top_body = Some(lowered.root_body());
    }

    let mut defs_by_span: HashMap<(TextRange, &'static str), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(String, &'static str), DefId> = HashMap::new();
    let mut file_defs: Vec<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .collect();
    file_defs.sort_by_key(|(id, data)| (data.span.start, data.span.end, id.0));
    for (def_id, data) in file_defs {
      let kind = match data.kind {
        DefKind::Function(_) => Some("fn"),
        DefKind::Var(_) => Some("var"),
        _ => None,
      };
      if let Some(kind) = kind {
        if kind == "var" {
          if let Some(hir_def) = lowered.def(*def_id) {
            if matches!(hir_def.path.kind, HirDefKind::VarDeclarator) {
              // `VarDeclarator` defs exist to own initializer bodies; they are not
              // bindings and shouldn't be used for mapping patterns to program
              // definitions.
              continue;
            }
          }
        }
        defs_by_span.entry((data.span, kind)).or_insert(*def_id);
        defs_by_name
          .entry((data.name.clone(), kind))
          .or_insert(*def_id);
      }
    }

    for (hir_body_id, idx) in lowered.body_index.iter() {
      let hir_body = lowered
        .bodies
        .get(*idx)
        .map(Arc::as_ref)
        .unwrap_or_else(|| panic!("missing lowered body for id {:?}", hir_body_id));

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Var(decl) = &stmt.kind {
          for declarator in decl.declarators.iter() {
            // Update every bound identifier in the declarator (including destructuring patterns)
            // with the initializer expression/body. This keeps `var_initializer` fast and avoids
            // relying on the salsa HIR scan for common destructuring cases.
            let mut stack = vec![declarator.pat];
            let mut updated: HashSet<DefId> = HashSet::new();
            while let Some(pat_id) = stack.pop() {
              let Some(pat) = hir_body.pats.get(pat_id.0 as usize) else {
                continue;
              };
              match &pat.kind {
                hir_js::PatKind::Ident(name_id) => {
                  let name = lowered.names.resolve(*name_id).map(|n| n.to_string());
                  let def_id = defs_by_span.get(&(pat.span, "var")).copied().or_else(|| {
                    name
                      .as_ref()
                      .and_then(|name| defs_by_name.get(&(name.clone(), "var")).copied())
                  });
                  let Some(def_id) = def_id else {
                    continue;
                  };
                  if !updated.insert(def_id) {
                    continue;
                  }
                  if let Some(def) = self.def_data.get_mut(&def_id) {
                    if let DefKind::Var(var) = &mut def.kind {
                      var.mode = match decl.kind {
                        hir_js::VarDeclKind::Var => VarDeclMode::Var,
                        hir_js::VarDeclKind::Let => VarDeclMode::Let,
                        hir_js::VarDeclKind::Const => VarDeclMode::Const,
                        hir_js::VarDeclKind::Using => VarDeclMode::Using,
                        hir_js::VarDeclKind::AwaitUsing => VarDeclMode::AwaitUsing,
                      };
                      if let Some(init) = declarator.init {
                        let prefer = matches!(hir_body.kind, HirBodyKind::Initializer);
                        if var.body == MISSING_BODY || prefer {
                          var.body = *hir_body_id;
                        }
                        if var.init.is_none() || prefer {
                          var.init = Some(init);
                        }
                      }
                    }
                  }
                }
                hir_js::PatKind::Array(arr) => {
                  for elem in arr.elements.iter() {
                    let Some(elem) = elem.as_ref() else {
                      continue;
                    };
                    stack.push(elem.pat);
                  }
                  if let Some(rest) = arr.rest {
                    stack.push(rest);
                  }
                }
                hir_js::PatKind::Object(obj) => {
                  for prop in obj.props.iter() {
                    stack.push(prop.value);
                  }
                  if let Some(rest) = obj.rest {
                    stack.push(rest);
                  }
                }
                hir_js::PatKind::Rest(inner) => {
                  stack.push(**inner);
                }
                hir_js::PatKind::Assign { target, .. } => {
                  stack.push(*target);
                }
                hir_js::PatKind::AssignTarget(_) => {}
              }
            }
          }
        }
      }

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Decl(def) = &stmt.kind {
          if let Some(hir_def) = lowered.def(*def) {
            if let Some(child) = hir_def.body {
              self.body_parents.insert(child, *hir_body_id);
            }
          }
        }
      }

      for expr in hir_body.exprs.iter() {
        match &expr.kind {
          HirExprKind::FunctionExpr { body, .. } | HirExprKind::ClassExpr { body, .. } => {
            self.body_parents.insert(*body, *hir_body_id);
          }
          _ => {}
        }
      }

      self.body_map.insert(
        *hir_body_id,
        BodyMeta {
          file,
          hir: Some(*hir_body_id),
          kind: hir_body.kind,
        },
      );
    }

    for export in lowered.hir.exports.iter() {
      if let HirExportKind::Default(default) = &export.kind {
        match &default.value {
          hir_js::ExportDefaultValue::Expr { expr, body } => {
            if let Some((_def_id, def)) = self
              .def_data
              .iter_mut()
              .find(|(_, data)| data.file == file && data.name == "default")
            {
              if let DefKind::Var(var) = &mut def.kind {
                var.body = *body;
                var.init = Some(*expr);
                var.mode = VarDeclMode::Const;
              }
              self.body_parents.insert(*body, lowered.root_body());
            }
          }
          hir_js::ExportDefaultValue::Class { def, body, .. }
          | hir_js::ExportDefaultValue::Function { def, body, .. } => {
            if let Some(data) = self.def_data.get_mut(def) {
              match &mut data.kind {
                DefKind::Function(func) => func.body = Some(*body),
                DefKind::Class(class) => class.body = Some(*body),
                _ => {}
              }
            }
            self.body_parents.insert(*body, lowered.root_body());
          }
        }
      }
    }

    // Connect definition-owned bodies (notably initializer bodies) to their containing body so
    // nested checks can seed outer bindings (parameters, locals, etc). Bodies introduced by
    // `StmtKind::Decl` and expression nodes are already linked above; this covers orphan bodies
    // such as `DefSource::Var` initializer bodies that otherwise lack a parent edge.
    let root_body = lowered.root_body();
    let mut def_to_body: HashMap<HirDefId, BodyId> = HashMap::new();
    for def in lowered.defs.iter() {
      if let Some(body) = def.body {
        def_to_body.insert(def.id, body);
      }
    }
    for def in lowered.defs.iter() {
      let Some(child_body) = def.body else {
        continue;
      };
      if child_body == root_body {
        continue;
      }
      let Some(parent_def) = def.parent else {
        continue;
      };
      let Some(parent_body) = def_to_body.get(&parent_def).copied() else {
        continue;
      };
      if child_body == parent_body {
        continue;
      }
      self.body_parents.entry(child_body).or_insert(parent_body);
    }

    // Fallback: infer missing parent links from body span containment.
    //
    // `hir-js` synthesizes bodies for variable initializers (and similar nodes) that are not
    // referenced by the surrounding statement list. Those bodies still need parent edges so
    // nested checks can seed parameter/local bindings.
    fn hir_body_range(body: &hir_js::Body) -> TextRange {
      let mut start = u32::MAX;
      let mut end = 0u32;
      for stmt in body.stmts.iter() {
        start = start.min(stmt.span.start);
        end = end.max(stmt.span.end);
      }
      for expr in body.exprs.iter() {
        start = start.min(expr.span.start);
        end = end.max(expr.span.end);
      }
      for pat in body.pats.iter() {
        start = start.min(pat.span.start);
        end = end.max(pat.span.end);
      }
      if start == u32::MAX {
        // Use the stored body span for synthesized bodies (notably initializer bodies) that don't
        // record statement/expression spans. This keeps span containment inference stable so
        // initializer bodies inherit bindings from their lexical parent.
        match body.kind {
          HirBodyKind::Class => TextRange::new(0, 0),
          _ => body.span,
        }
      } else {
        TextRange::new(start, end)
      }
    }

    let mut bodies: Vec<(BodyId, TextRange)> = lowered
      .body_index
      .keys()
      .copied()
      .filter_map(|id| lowered.body(id).map(|b| (id, hir_body_range(b))))
      .collect();
    bodies.sort_by_key(|(id, range)| (range.start, Reverse(range.end), id.0));

    let mut stack: Vec<(BodyId, TextRange)> = Vec::new();
    for (child, range) in bodies {
      if child == root_body {
        stack.clear();
        stack.push((child, range));
        continue;
      }
      while let Some((_, parent_range)) = stack.last().copied() {
        if range.start >= parent_range.start && range.end <= parent_range.end {
          break;
        }
        stack.pop();
      }
      let computed_parent = stack.last().map(|(id, _)| *id).unwrap_or(root_body);
      if computed_parent != child {
        let is_initializer = lowered
          .body(child)
          .map(|body| matches!(body.kind, HirBodyKind::Initializer))
          .unwrap_or(false);
        // Initializer bodies must inherit bindings from their containing scope
        // (e.g. function parameters). The def-parent chain can be incomplete or
        // point at a broader container, so prefer the lexical parent inferred
        // from span containment for initializer bodies.
        if is_initializer || !self.body_parents.contains_key(&child) {
          self.body_parents.insert(child, computed_parent);
        }
      }
      stack.push((child, range));
    }

    // Keep the body parent graph consistent with the query-side computation used
    // by `db::body_parents_in_file`. The salsa query includes additional edges
    // (e.g. getter/setter bodies and synthesized initializer bodies) and is the
    // canonical implementation. Overwrite any locally inferred edges for this
    // file so nested checks can reliably seed outer bindings.
    let parents = db::body_parents_in_file(&self.typecheck_db, file);
    for (child, parent) in parents.iter() {
      self.body_parents.insert(*child, *parent);
    }

    self.next_body = self
      .body_map
      .keys()
      .map(|b| b.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  pub(super) fn rebuild_body_owners(&mut self) {
    self.body_owners.clear();
    let mut defs: Vec<_> = self.def_data.iter().collect();
    defs.sort_by_key(|(id, data)| (data.file.0, data.span.start, data.span.end, id.0));
    for (def_id, data) in defs {
      match &data.kind {
        DefKind::Function(func) => {
          if let Some(body) = func.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Var(var) => {
          if var.body != MISSING_BODY {
            self.body_owners.insert(var.body, *def_id);
          }
        }
        DefKind::VarDeclarator(var) => {
          if let Some(body) = var.body {
            self.body_owners.entry(body).or_insert(*def_id);
          }
        }
        DefKind::Class(class) => {
          if let Some(body) = class.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Enum(en) => {
          if let Some(body) = en.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Namespace(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Module(ns) => {
          if let Some(body) = ns.body {
            self.body_owners.insert(body, *def_id);
          }
        }
        DefKind::Import(_)
        | DefKind::ImportAlias(_)
        | DefKind::Interface(_)
        | DefKind::TypeAlias(_) => {}
      }
    }
  }

}
