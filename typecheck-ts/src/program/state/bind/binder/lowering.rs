use super::*;

impl ProgramState {
  pub(super) fn lower_function(&mut self, file: FileId, func: &Func, _def: DefId) -> FuncData {
    let mut params = Vec::new();
    for (idx, param) in func.parameters.iter().enumerate() {
      params.push(self.lower_param(file, param, idx));
    }
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    FuncData {
      params,
      return_ann,
      body: None,
    }
  }

  pub(super) fn lower_param(&mut self, file: FileId, param: &Node<ParamDecl>, index: usize) -> ParamData {
    let (name, symbol, record_symbol) = match param.stx.pattern.stx.pat.stx.as_ref() {
      Pat::Id(id) => (id.stx.name.clone(), self.alloc_symbol(), true),
      _ => (format!("<pattern{index}>"), self.alloc_symbol(), false),
    };
    let typ = param
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
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
