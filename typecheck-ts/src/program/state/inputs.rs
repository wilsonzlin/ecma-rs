use super::*;

impl ProgramState {
  pub(super) fn load_text(
    &self,
    file: FileId,
    host: &Arc<dyn Host>,
  ) -> Result<Arc<str>, HostError> {
    let Some(key) = self.file_key_for_id(file) else {
      return Err(HostError::new(format!("missing file key for {file:?}")));
    };
    let origin = self
      .file_registry
      .lookup_origin(file)
      .unwrap_or(FileOrigin::Source);
    if matches!(origin, FileOrigin::Lib) {
      if let Some(text) = self.lib_texts.get(&file) {
        return Ok(text.clone());
      }
    }
    if let Some(text) = self.file_overrides.get(&key) {
      return Ok(text.clone());
    }
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    host.file_text(&key)
  }

  pub(super) fn record_module_resolution(
    &mut self,
    from: FileId,
    specifier: &str,
    host: &Arc<dyn Host>,
  ) -> Option<FileId> {
    let resolved_key = self
      .file_key_for_id(from)
      .and_then(|from_key| host.resolve(&from_key, specifier));
    let mut resolved = resolved_key.as_ref().map(|target_key| {
      // Prefer an already-known file ID when the host resolution points at a
      // library file key. Many hosts provide `.d.ts` libraries via
      // `Host::lib_files()` only (without implementing `file_text` for them),
      // so interning them as `Source` would create a second `FileId` that
      // cannot be loaded.
      self
        .file_id_for_key(target_key)
        .unwrap_or_else(|| self.intern_file_key(target_key.clone(), FileOrigin::Source))
    });
    if let (Some(file), Some(target_key)) = (resolved, resolved_key.as_ref()) {
      if db::Db::file_input(&self.typecheck_db, file).is_none() {
        // Lib file inputs are seeded up-front in `process_libs`. When resolving
        // module specifiers during lib processing we may see dependent lib IDs
        // before their texts are staged, so only auto-seed source files here.
        let origin = self
          .file_registry
          .lookup_origin(file)
          .unwrap_or(FileOrigin::Source);
        if matches!(origin, FileOrigin::Source) {
          let kind = *self
            .file_kinds
            .entry(file)
            .or_insert_with(|| host.file_kind(target_key));
          match self.load_text(file, host) {
            Ok(text) => self.set_salsa_inputs(file, kind, text),
            Err(_) => resolved = None,
          }
        }
      }
    }
    self
      .typecheck_db
      .set_module_resolution_ref(from, specifier, resolved);
    resolved
  }

  pub(super) fn set_salsa_inputs(&mut self, file: FileId, kind: FileKind, text: Arc<str>) {
    let key = self
      .file_registry
      .lookup_key(file)
      .unwrap_or_else(|| panic!("file {:?} must be interned before setting inputs", file));
    let origin = self
      .file_registry
      .lookup_origin(file)
      .unwrap_or(FileOrigin::Source);
    if let Some(existing) = db::Db::file_input(&self.typecheck_db, file) {
      let existing_key = existing.key(&self.typecheck_db);
      let existing_kind = existing.kind(&self.typecheck_db);
      let existing_text = existing.text(&self.typecheck_db);
      if existing_kind == kind
        && existing_key == key
        && existing_text.as_ref() == text.as_ref()
        && db::Db::file_origin(&self.typecheck_db, file) == Some(origin)
      {
        return;
      }
    }

    self.typecheck_db.set_file(file, key, kind, text, origin);
  }

  pub(super) fn parse_via_salsa(
    &mut self,
    file: FileId,
    kind: FileKind,
    text: Arc<str>,
  ) -> Result<Arc<Node<TopLevel>>, Diagnostic> {
    self.set_salsa_inputs(file, kind, Arc::clone(&text));
    let result = db::parse(&self.typecheck_db, file);
    match result.ast {
      Some(ast) => Ok(ast),
      None => Err(result.diagnostics.into_iter().next().unwrap_or_else(|| {
        codes::MISSING_BODY.error("missing parsed AST", Span::new(file, TextRange::new(0, 0)))
      })),
    }
  }
}
