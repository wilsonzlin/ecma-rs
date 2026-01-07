use super::*;

impl ProgramState {
  pub(in super::super) fn init_is_satisfies(&self, body: BodyId, expr: ExprId) -> bool {
    let meta = match self.body_map.get(&body) {
      Some(meta) => meta,
      None => return false,
    };
    let hir_id = match meta.hir {
      Some(id) => id,
      None => return false,
    };
    let lowered = match self.hir_lowered.get(&meta.file) {
      Some(lowered) => lowered,
      None => return false,
    };
    let hir_body = match lowered.body(hir_id) {
      Some(body) => body,
      None => return false,
    };
    hir_body
      .exprs
      .get(expr.0 as usize)
      .map(|e| matches!(e.kind, HirExprKind::Satisfies { .. }))
      .unwrap_or(false)
  }

  pub(in super::super) fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    if let Some(def_data) = self.def_data.get(&def) {
      if let DefKind::Var(var) = &def_data.kind {
        if var.body != MISSING_BODY {
          if let Some(expr) = var.init {
            let decl_kind = match var.mode {
              VarDeclMode::Var => HirVarDeclKind::Var,
              VarDeclMode::Let => HirVarDeclKind::Let,
              VarDeclMode::Const => HirVarDeclKind::Const,
              VarDeclMode::Using => HirVarDeclKind::Using,
              VarDeclMode::AwaitUsing => HirVarDeclKind::AwaitUsing,
            };
            let pat = if self.snapshot_loaded {
              self
                .body_results
                .get(&var.body)
                .and_then(|result| {
                  result
                    .pat_spans
                    .iter()
                    .position(|span| *span == def_data.span)
                })
                .map(|idx| PatId(idx as u32))
            } else {
              self.body_map.get(&var.body).and_then(|meta| {
                let hir_id = meta.hir?;
                self
                  .hir_lowered
                  .get(&meta.file)
                  .and_then(|lowered| lowered.body(hir_id))
                  .and_then(|body| {
                    body.pats.iter().enumerate().find_map(|(idx, pat)| {
                      (pat.span == def_data.span).then_some(PatId(idx as u32))
                    })
                  })
              })
            };
            return Some(VarInit {
              body: var.body,
              expr,
              decl_kind,
              pat,
              span: Some(def_data.span),
            });
          }
        }
      }
    }

    if self.snapshot_loaded {
      return None;
    }

    if let Some(init) = crate::db::var_initializer(&self.typecheck_db, def) {
      if std::env::var("DEBUG_OVERLOAD").is_ok() {
        if let Some(data) = self.def_data.get(&def) {
          eprintln!("DEBUG var initializer for {} -> {:?}", data.name, init);
        }
      }
      return Some(init);
    }

    let def_data = self.def_data.get(&def)?;
    let lowered = self.hir_lowered.get(&def_data.file)?;
    let hir_def = lowered.def(def)?;
    let def_name = lowered.names.resolve(hir_def.path.name);
    if !matches!(
      hir_def.path.kind,
      HirDefKind::Var | HirDefKind::VarDeclarator
    ) && def_name != Some("default")
    {
      return None;
    }
    let def_name = def_name.or_else(|| Some(def_data.name.as_str()));
    var_initializer_in_file(lowered, def, hir_def.span, def_name)
  }
}
