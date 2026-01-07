use super::*;

impl ProgramState {
  pub(super) fn bind_namespace_member_defs(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    file_kind: sem_ts::FileKind,
    defs: &mut Vec<DefId>,
  ) {
    fn bind_body(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      defs: &mut Vec<DefId>,
      builder: &mut SemHirBuilder,
    ) {
      match body {
        NamespaceBody::Block(stmts) => {
          for stmt in stmts.iter() {
            match stmt.stx.as_ref() {
              Stmt::VarDecl(var) => {
                let new_defs = state.handle_var_decl(file, var.stx.as_ref(), builder);
                for (def_id, _binding, _export_name) in new_defs {
                  defs.push(def_id);
                }
              }
              Stmt::FunctionDecl(func) => {
                let span = loc_to_span(file, stmt.loc);
                if let Some((def_id, _binding, _export_name)) =
                  state.handle_function_decl(file, span.range, func.stx.as_ref(), builder)
                {
                  defs.push(def_id);
                }
              }
              Stmt::NamespaceDecl(ns) => {
                let span = loc_to_span(file, stmt.loc);
                let name = ns.stx.name.clone();
                let symbol = state.alloc_symbol();
                let def_id = state.alloc_def();
                state.def_data.insert(
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
                state.record_def_symbol(def_id, symbol);
                state.record_symbol(file, span.range, symbol);
                defs.push(def_id);
                bind_body(state, file, &ns.stx.body, defs, builder);
              }
              _ => {}
            }
          }
        }
        NamespaceBody::Namespace(inner) => {
          let span = loc_to_span(file, inner.loc);
          let name = inner.stx.name.clone();
          let symbol = state.alloc_symbol();
          let def_id = state.alloc_def();
          state.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: inner.stx.export,
              kind: DefKind::Namespace(NamespaceData {
                body: None,
                value_type: None,
                type_type: None,
                declare: inner.stx.declare,
              }),
            },
          );
          state.record_def_symbol(def_id, symbol);
          state.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bind_body(state, file, &inner.stx.body, defs, builder);
        }
      }
    }

    let mut dummy_builder = SemHirBuilder::new(file, file_kind);
    bind_body(self, file, body, defs, &mut dummy_builder);
  }
}
