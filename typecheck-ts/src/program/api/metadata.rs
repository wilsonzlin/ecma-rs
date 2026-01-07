use super::*;

impl Program {
  /// Definitions declared in a file.
  pub fn definitions_in_file(&self, file: FileId) -> Vec<DefId> {
    match self.definitions_in_file_fallible(file) {
      Ok(defs) => defs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn definitions_in_file_fallible(&self, file: FileId) -> Result<Vec<DefId>, FatalError> {
    self.with_analyzed_state(|state| {
      let mut defs = state
        .files
        .get(&file)
        .map(|f| f.defs.clone())
        .unwrap_or_default();
      defs.sort_by_key(|id| id.0);
      Ok(defs)
    })
  }

  /// Bodies belonging to a file.
  pub fn bodies_in_file(&self, file: FileId) -> Vec<BodyId> {
    match self.with_analyzed_state(|state| {
      let mut bodies: Vec<BodyId> = state
        .body_map
        .iter()
        .filter_map(|(id, meta)| (meta.file == file).then_some(*id))
        .collect();
      bodies.sort_by_key(|id| id.0);
      Ok(bodies)
    }) {
      Ok(bodies) => bodies,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Expression IDs in a body.
  pub fn exprs_in_body(&self, body: BodyId) -> Vec<ExprId> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(result) = state.body_results.get(&body) {
          return Ok((0..result.expr_types.len() as u32).map(ExprId).collect());
        }
      }
      let ids = state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .map(|body| (0..body.exprs.len() as u32).map(ExprId).collect())
        })
      });
      Ok(ids.unwrap_or_default())
    }) {
      Ok(exprs) => exprs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Pattern IDs in a body.
  pub fn pats_in_body(&self, body: BodyId) -> Vec<PatId> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(result) = state.body_results.get(&body) {
          return Ok((0..result.pat_types.len() as u32).map(PatId).collect());
        }
      }
      let ids = state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .map(|body| (0..body.pats.len() as u32).map(PatId).collect())
        })
      });
      Ok(ids.unwrap_or_default())
    }) {
      Ok(pats) => pats,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Span for a definition, if available.
  pub fn def_span(&self, def: DefId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).map(|data| Span {
        file: data.file,
        range: data.span,
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Locate the initializer for a variable definition, if any.
  pub fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    match self.var_initializer_fallible(def) {
      Ok(init) => init,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn var_initializer_fallible(&self, def: DefId) -> Result<Option<VarInit>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.var_initializer(def)))
  }

  /// Span for an expression, if available.
  pub fn expr_span(&self, body: BodyId, expr: ExprId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        let Some(meta) = state.body_map.get(&body) else {
          return Ok(None);
        };
        if let Some(result) = state.body_results.get(&body) {
          if let Some(range) = result.expr_span(expr) {
            return Ok(Some(Span {
              file: meta.file,
              range,
            }));
          }
        }
      }

      Ok(state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .and_then(|body| {
              body.exprs.get(expr.0 as usize).map(|expr| Span {
                file: meta.file,
                range: expr.span,
              })
            })
        })
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Span for a pattern, if available.
  pub fn pat_span(&self, body: BodyId, pat: PatId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        let Some(meta) = state.body_map.get(&body) else {
          return Ok(None);
        };
        if let Some(result) = state.body_results.get(&body) {
          if let Some(range) = result.pat_span(pat) {
            return Ok(Some(Span {
              file: meta.file,
              range,
            }));
          }
        }
      }

      Ok(state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .and_then(|body| {
              body.pats.get(pat.0 as usize).map(|pat| Span {
                file: meta.file,
                range: pat.span,
              })
            })
        })
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Friendly name for a definition.
  pub fn def_name(&self, def: DefId) -> Option<String> {
    match self.def_name_fallible(def) {
      Ok(name) => name,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn def_name_fallible(&self, def: DefId) -> Result<Option<String>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).and_then(|d| {
        // `hir-js` `VarDeclarator` nodes are internal containers for variable declarations and do
        // not correspond to user-visible bindings; hide them from the name lookup helper so
        // callers searching by name (tests included) find the actual `Var` binding.
        (!matches!(d.kind, DefKind::VarDeclarator(_))).then(|| d.name.clone())
      }))
    })
  }

  /// Kind of a definition, if known.
  pub fn def_kind(&self, def: DefId) -> Option<DefKind> {
    match self.def_kind_fallible(def) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn def_kind_fallible(&self, def: DefId) -> Result<Option<DefKind>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.def_data.get(&def).map(|d| d.kind.clone())))
  }

  /// Body attached to a definition, if any.
  pub fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    match self.body_of_def_fallible(def) {
      Ok(body) => body,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn body_of_def_fallible(&self, def: DefId) -> Result<Option<BodyId>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).and_then(|d| match &d.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) => {
          if var.body != MISSING_BODY {
            Some(var.body)
          } else {
            state.var_initializer(def).map(|init| init.body)
          }
        }
        DefKind::VarDeclarator(var) => var.body,
        DefKind::Class(class) => class.body,
        DefKind::Enum(en) => en.body,
        DefKind::Namespace(ns) => ns.body,
        DefKind::Module(module) => module.body,
        DefKind::Import(_) | DefKind::ImportAlias(_) => None,
        DefKind::Interface(_) => None,
        DefKind::TypeAlias(_) => None,
      }))
    })
  }

  /// Implicit top-level body for a file, if any.
  pub fn file_body(&self, file: FileId) -> Option<BodyId> {
    match self.file_body_fallible(file) {
      Ok(body) => body,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn file_body_fallible(&self, file: FileId) -> Result<Option<BodyId>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.files.get(&file).and_then(|f| f.top_body)))
  }

  /// Span of a definition, if known.
  pub fn span_of_def(&self, def: DefId) -> Option<Span> {
    match self.span_of_def_fallible(def) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn span_of_def_fallible(&self, def: DefId) -> Result<Option<Span>, FatalError> {
    self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        return Ok(
          state
            .def_data
            .get(&def)
            .map(|data| Span::new(data.file, data.span)),
        );
      }
      if let Some(span) = db::span_of_def(&state.typecheck_db, def) {
        return Ok(Some(span));
      }
      Ok(
        state
          .def_data
          .get(&def)
          .map(|data| Span::new(data.file, data.span)),
      )
    })
  }

  /// Span of an expression within a body, if available from cached results.
  pub fn span_of_expr(&self, body: BodyId, expr: ExprId) -> Option<Span> {
    match self.span_of_expr_fallible(body, expr) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn span_of_expr_fallible(
    &self,
    body: BodyId,
    expr: ExprId,
  ) -> Result<Option<Span>, FatalError> {
    self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        let Some(meta) = state.body_map.get(&body).copied() else {
          return Ok(None);
        };
        let res = state.check_body(body)?;
        return Ok(res.expr_span(expr).map(|range| Span::new(meta.file, range)));
      }
      if let Some(span) = db::span_of_expr(&state.typecheck_db, body, expr) {
        return Ok(Some(span));
      }
      let Some(meta) = state.body_map.get(&body).copied() else {
        return Ok(None);
      };
      let res = state.check_body(body)?;
      Ok(res.expr_span(expr).map(|range| Span::new(meta.file, range)))
    })
  }
}
