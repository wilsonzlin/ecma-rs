use super::*;

impl ProgramState {
  pub(super) fn handle_var_decl(
    &mut self,
    file: FileId,
    var: &VarDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Vec<(DefId, (String, SymbolBinding), Option<String>)> {
    fn collect_bound_names(
      state: &mut ProgramState,
      file: FileId,
      pat: &Node<Pat>,
      out: &mut Vec<(String, TextRange)>,
    ) {
      match pat.stx.as_ref() {
        Pat::Id(id) => {
          out.push((id.stx.name.clone(), loc_to_span(file, id.loc).range));
        }
        Pat::Arr(arr) => {
          for elem in arr.stx.elements.iter() {
            let Some(elem) = elem.as_ref() else {
              continue;
            };
            collect_bound_names(state, file, &elem.target, out);
          }
          if let Some(rest) = arr.stx.rest.as_ref() {
            collect_bound_names(state, file, rest, out);
          }
        }
        Pat::Obj(obj) => {
          for prop in obj.stx.properties.iter() {
            collect_bound_names(state, file, &prop.stx.target, out);
          }
          if let Some(rest) = obj.stx.rest.as_ref() {
            collect_bound_names(state, file, rest, out);
          }
        }
        Pat::AssignTarget(_) => {
          state.diagnostics.push(
            codes::UNSUPPORTED_PATTERN.error("unsupported pattern", loc_to_span(file, pat.loc)),
          );
        }
      }
    }

    let mut defs = Vec::new();
    for declarator in var.declarators.iter() {
      let pat = &declarator.pattern;
      let type_ann = match pat.stx.pat.stx.as_ref() {
        Pat::Id(_) => declarator
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t)),
        _ => None,
      };
      let mut names = Vec::new();
      collect_bound_names(self, file, &pat.stx.pat, &mut names);
      for (name, def_span) in names {
        let symbol = self.alloc_symbol();
        let def_id = self.alloc_def();
        self.record_symbol(file, def_span, symbol);
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: def_span,
            symbol,
            export: var.export,
            kind: DefKind::Var(VarData {
              typ: type_ann,
              init: None,
              body: MISSING_BODY,
              mode: var.mode,
            }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        defs.push((
          def_id,
          (
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: type_ann,
            },
          ),
          if var.export { Some(name.clone()) } else { None },
        ));
        sem_builder.add_decl(
          def_id,
          name.clone(),
          sem_ts::DeclKind::Var,
          if var.export {
            sem_ts::Exported::Named
          } else {
            sem_ts::Exported::No
          },
          def_span,
        );
      }
    }
    defs
  }

  pub(super) fn handle_function_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    func: &FuncDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Option<(DefId, (String, SymbolBinding), Option<String>)> {
    let name_node = func.name.as_ref()?;
    let name = name_node.stx.name.clone();
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
    let def_id = self.alloc_def();
    let func_data = self.lower_function(file, func.function.stx.as_ref(), def_id);
    self.def_data.insert(
      def_id,
      DefData {
        name: name.clone(),
        file,
        span,
        symbol,
        export: func.export || func.export_default,
        kind: DefKind::Function(func_data),
      },
    );
    self.record_def_symbol(def_id, symbol);
    sem_builder.add_decl(
      def_id,
      name.clone(),
      sem_ts::DeclKind::Function,
      if func.export_default {
        sem_ts::Exported::Default
      } else if func.export {
        sem_ts::Exported::Named
      } else {
        sem_ts::Exported::No
      },
      loc_to_span(file, name_node.loc).range,
    );
    let binding = (
      name.clone(),
      SymbolBinding {
        symbol,
        def: Some(def_id),
        type_id: None,
      },
    );
    let export_name = if func.export_default {
      Some("default".to_string())
    } else if func.export {
      Some(name.clone())
    } else {
      None
    };
    Some((def_id, binding, export_name))
  }

}
