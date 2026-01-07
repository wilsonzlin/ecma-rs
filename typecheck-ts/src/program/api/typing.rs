use super::*;

impl Program {
  /// Type for a definition.
  pub fn type_of_def(&self, def: DefId) -> TypeId {
    match self.type_of_def_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        self.builtin_unknown()
      }
    }
  }

  pub fn type_of_def_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| ProgramState::type_of_def(state, def))
  }

  /// Check a body, returning the cached result.
  pub fn check_body(&self, body: BodyId) -> Arc<BodyCheckResult> {
    match self.check_body_fallible(body) {
      Ok(res) => res,
      Err(fatal) => {
        let diagnostics = self.fatal_to_diagnostics(fatal);
        Arc::new(BodyCheckResult {
          body,
          expr_types: Vec::new(),
          expr_spans: Vec::new(),
          pat_types: Vec::new(),
          pat_spans: Vec::new(),
          diagnostics,
          return_types: Vec::new(),
        })
      }
    }
  }

  pub fn check_body_fallible(&self, body: BodyId) -> Result<Arc<BodyCheckResult>, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let parallel_guard = db::queries::body_check::parallel_guard();
      if parallel_guard.is_some() {
        std::thread::yield_now();
      }
      let context = {
        let mut state = self.lock_state();
        state.ensure_interned_types(&self.host, &self.roots)?;
        if let Some(res) = state.body_results.get(&body).cloned() {
          return Ok(res);
        }
        state.body_check_context()
      };
      let db = BodyCheckDb::from_shared_context(context);
      let res = db::queries::body_check::check_body(&db, body);
      let mut state = self.lock_state();
      state.body_results.insert(body, Arc::clone(&res));
      Ok(res)
    })
  }

  /// Type of a specific expression in a body.
  pub fn type_of_expr(&self, body: BodyId, expr: ExprId) -> TypeId {
    match self.type_of_expr_fallible(body, expr) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        self.builtin_unknown()
      }
    }
  }

  pub fn type_of_expr_fallible(&self, body: BodyId, expr: ExprId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let result = state.check_body(body)?;
      let unknown = state.interned_unknown();
      Ok(result.expr_type(expr).unwrap_or(unknown))
    })
  }
}
