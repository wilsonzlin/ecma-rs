use super::*;

impl ProgramState {
  pub(in super::super) fn align_definitions_with_hir(
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
            typ: self.interned_unknown(),
          }),
          DefMatchKind::TypeAlias => DefKind::TypeAlias(TypeAliasData {
            typ: self.interned_unknown(),
          }),
          _ if def.path.kind == HirDefKind::EnumMember => {
            // Enum members are not untyped bindings. Without a declared type they
            // were lowered as bare `Var`s and `--noImplicitAny` falsely emitted
            // TC3000 on `A = "A"` / `B = "B"` (e.g. SPI fixture C13).
            DefKind::Var(VarData {
              typ: enum_member_declared_type(self, lowered, def),
              init: None,
              body: def.body.unwrap_or(MISSING_BODY),
              mode: VarDeclMode::Const,
            })
          }
          _ if def.path.kind == HirDefKind::StaticBlock => {
            // Static blocks are not value bindings; typing them as bare `Var`s
            // produced spurious TC3000 on `<static_block>` under `--noImplicitAny`.
            DefKind::Var(VarData {
              typ: Some(self.store.primitive_ids().void),
              init: None,
              body: def.body.unwrap_or(MISSING_BODY),
              mode: VarDeclMode::Var,
            })
          }
          _ if def.path.kind == HirDefKind::Field => {
            // Ambient / `declare class` fields are not subject to TS7008
            // (`privateNameAmbientNoImplicitAny`). Seed `any` so `type_of_def`
            // does not emit. Concrete unannotated fields still go through
            // `--noImplicitAny` as TS7008 (not TC3000).
            DefKind::Var(VarData {
              typ: if def.is_ambient {
                Some(self.store.primitive_ids().any)
              } else {
                None
              },
              init: None,
              body: def.body.unwrap_or(MISSING_BODY),
              mode: VarDeclMode::Var,
            })
          }
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
          let new_is_type_only = matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_));
          bindings
            .entry(raw_name.clone())
            .and_modify(|binding| {
              binding.symbol = data.symbol;
              // TYPE-only decls must not clobber an existing VALUE binding
              // (`class C` + `interface C` declaration merging). Otherwise the
              // later `value_defs` remap never sees the class DefId and
              // `new C()` resolves through the interface type.
              let existing_is_value = binding.def.is_some_and(|existing| {
                new_def_data.get(&existing).is_some_and(|existing_data| {
                  !matches!(
                    existing_data.kind,
                    DefKind::Interface(_) | DefKind::TypeAlias(_)
                  )
                })
              });
              // tsc: a repeatedly-declared `var` keeps its *first*
              // declaration's type (subsequent declarations are TS2403
              // candidates, not the binding's type). Later `var` decls must
              // not clobber the first `var`'s def — otherwise seeded bindings
              // carry the *last* declaration's type
              // (`forStatementsMultipleInvalidDecl`).
              let keep_first_var = matches!(data.kind, DefKind::Var(_))
                && binding.def.is_some_and(|existing| {
                  new_def_data
                    .get(&existing)
                    .is_some_and(|existing_data| matches!(existing_data.kind, DefKind::Var(_)))
                });
              if !(new_is_type_only && existing_is_value) && !keep_first_var {
                binding.def = Some(def_id);
              }
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
        let new_is_type_only = matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_));
        let existing_is_value = exports.get(&export_name).is_some_and(|entry| {
          entry.def.is_some_and(|existing| {
            new_def_data.get(&existing).is_some_and(|existing_data| {
              !matches!(
                existing_data.kind,
                DefKind::Interface(_) | DefKind::TypeAlias(_)
              )
            })
          })
        });
        if !(new_is_type_only && existing_is_value) {
          exports.insert(
            export_name,
            ExportEntry {
              symbol: data.symbol,
              def: Some(def_id),
              type_id: new_interned_def_types.get(&def_id).copied(),
            },
          );
        }
      }

      new_def_data.insert(def_id, data);
      resolved_defs.push(def_id);
    }

    for leftovers in by_name_kind.values_mut() {
      for (old_id, data) in leftovers.drain(..) {
        new_def_data.insert(old_id, data.clone());
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
    self.interned_def_types = new_interned_def_types;
    self.interned_type_params = new_interned_type_params;
    self.interned_type_param_decls = new_interned_type_param_decls;
    self.interned_enum_defs = self
      .def_data
      .iter()
      .filter_map(|(id, data)| matches!(data.kind, DefKind::Enum(_)).then_some(*id))
      .collect();

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
}

/// Declared type for an enum member def, used so `--noImplicitAny` does not
/// treat `A = "A"` as an untyped binding (TC3000).
fn enum_member_declared_type(
  state: &ProgramState,
  lowered: &LowerResult,
  def: &hir_js::DefData,
) -> Option<tti::TypeId> {
  let parent = def.parent?;
  let parent_def = lowered.def(parent)?;
  let hir_js::DefTypeInfo::Enum { members } = parent_def.type_info.as_ref()? else {
    return None;
  };
  let member = members.iter().find(|m| m.name == def.name)?;
  let prim = state.store.primitive_ids();
  Some(match &member.value {
    hir_js::EnumMemberValue::Number(n) => state.store.intern_type(tti::TypeKind::NumberLiteral(
      ordered_float::OrderedFloat::from(*n),
    )),
    hir_js::EnumMemberValue::String(s) => {
      let id = state.store.intern_name(s.clone());
      state.store.intern_type(tti::TypeKind::StringLiteral(id))
    }
    hir_js::EnumMemberValue::Computed => prim.any,
  })
}
