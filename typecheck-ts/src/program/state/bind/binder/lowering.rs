use super::*;

impl ProgramState {
  pub(super) fn lower_function(&mut self, file: FileId, func: &Func, _def: DefId) -> FuncData {
    // HIR-only binder slice: when the file is already lowered, leave param/return
    // annotations unset. `function_type` / `type_of_def` recompute from
    // `hir_js::FunctionData` (semantics/bindings are incomplete here).
    let use_hir = self.hir_lowered.contains_key(&file);
    let mut params = Vec::new();
    for (idx, param) in func.parameters.iter().enumerate() {
      params.push(self.lower_param(file, param, idx, use_hir));
    }
    let return_ann = if use_hir {
      None
    } else {
      func
        .return_type
        .as_ref()
        .map(|t| self.type_from_type_expr(t))
    };
    FuncData {
      params,
      return_ann,
      body: None,
    }
  }

  pub(super) fn lower_param(
    &mut self,
    file: FileId,
    param: &Node<ParamDecl>,
    index: usize,
    use_hir: bool,
  ) -> ParamData {
    let (name, symbol, record_symbol) = match param.stx.pattern.stx.pat.stx.as_ref() {
      Pat::Id(id) => (id.stx.name.clone(), self.alloc_symbol(), true),
      _ => (format!("<pattern{index}>"), self.alloc_symbol(), false),
    };
    let typ = if use_hir {
      None
    } else {
      param
        .stx
        .type_annotation
        .as_ref()
        .map(|t| self.type_from_type_expr(t))
    };
    if record_symbol {
      self.record_symbol(file, loc_to_span(file, param.stx.pattern.loc).range, symbol);
    }
    ParamData {
      name,
      typ,
      symbol,
      pat: None,
    }
  }
}
