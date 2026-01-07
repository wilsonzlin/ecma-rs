use super::*;

impl ProgramState {
  pub(in super::super) fn find_namespace_def(&self, file: FileId, name: &str) -> Option<DefId> {
    self
      .def_data
      .iter()
      .find_map(|(id, data)| match &data.kind {
        DefKind::Namespace(_) | DefKind::Module(_) if data.file == file && data.name == name => {
          Some(*id)
        }
        _ => None,
      })
  }

  pub(in super::super) fn merge_namespace_value_types(&mut self) -> Result<(), FatalError> {
    let store = Arc::clone(&self.store);
    fn is_ident_char(byte: u8) -> bool {
      byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$')
    }

    fn find_name_span(source: &str, name: &str, range: TextRange) -> TextRange {
      let bytes = source.as_bytes();
      let start = (range.start as usize).min(bytes.len());
      let end = (range.end as usize).min(bytes.len());
      let slice = &source[start..end];
      let mut offset = 0usize;
      while offset <= slice.len() {
        let Some(pos) = slice[offset..].find(name) else {
          break;
        };
        let abs_start = start + offset + pos;
        let abs_end = abs_start + name.len();
        if abs_end > bytes.len() {
          break;
        }
        let before_ok = abs_start == 0 || !is_ident_char(bytes[abs_start - 1]);
        let after_ok = abs_end == bytes.len() || !is_ident_char(bytes[abs_end]);
        if before_ok && after_ok {
          return TextRange::new(abs_start as u32, abs_end as u32);
        }
        offset = offset.saturating_add(pos.saturating_add(name.len().max(1)));
      }
      range
    }

    let is_top_level = |state: &ProgramState, file: FileId, def: DefId| -> bool {
      let Some(lowered) = state.hir_lowered.get(&file) else {
        return true;
      };
      let Some(hir_def) = lowered.def(def) else {
        return true;
      };
      let mut parent = hir_def.parent;
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
      true
    };

    let mut entries: Vec<_> = self
      .namespace_object_types
      .iter()
      .map(|(k, v)| (k.clone(), *v))
      .collect();
    entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
    for ((file, name), ns_ty) in entries.into_iter() {
      let ns_def = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          (data.file == file
            && data.name == name
            && matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
            && is_top_level(self, file, *id))
          .then_some(*id)
        })
        .min_by_key(|id| {
          let span = self
            .def_data
            .get(id)
            .map(|d| d.span)
            .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
          (span.start, span.end, id.0)
        });
      let value_def = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          (data.file == file
            && data.name == name
            && matches!(
              data.kind,
              DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_)
            )
            && is_top_level(self, file, *id))
          .then_some(*id)
        })
        .min_by_key(|id| {
          let span = self
            .def_data
            .get(id)
            .map(|d| d.span)
            .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
          (span.start, span.end, id.0)
        });

      if let (Some(ns_def), Some(val_def)) = (ns_def, value_def) {
        let Some((ns_span, ns_export)) = self
          .def_data
          .get(&ns_def)
          .map(|data| (data.span, data.export))
        else {
          continue;
        };
        let Some((val_span, val_export)) = self
          .def_data
          .get(&val_def)
          .map(|data| (data.span, data.export))
        else {
          continue;
        };

        let file_text = db::file_text(&self.typecheck_db, file);
        let namespace_name_span = find_name_span(file_text.as_ref(), &name, ns_span);
        let value_name_span = find_name_span(file_text.as_ref(), &name, val_span);

        let mut has_error = false;
        if ns_export != val_export {
          has_error = true;
          self.push_program_diagnostic(codes::MERGED_DECLARATIONS_EXPORT_MISMATCH.error(
            format!(
              "Individual declarations in merged declaration '{name}' must be all exported or all local."
            ),
            Span::new(file, namespace_name_span),
          ));
          self.push_program_diagnostic(codes::MERGED_DECLARATIONS_EXPORT_MISMATCH.error(
            format!(
              "Individual declarations in merged declaration '{name}' must be all exported or all local."
            ),
            Span::new(file, value_name_span),
          ));
        }

        if ns_span.start < val_span.start {
          // Match tsc: TS2434 still reports, but the merge continues so namespace
          // members remain visible on the merged value.
          self.push_program_diagnostic(codes::NAMESPACE_BEFORE_MERGE_TARGET.error(
            "A namespace declaration cannot be located prior to a class or function with which it is merged.",
            Span::new(file, namespace_name_span),
          ));
        }

        if has_error {
          continue;
        }

        if let Some(val_ty) = self.interned_def_types.get(&val_def).copied() {
          let merged = store.intersection(vec![val_ty, ns_ty]);
          self.interned_def_types.insert(ns_def, merged);
          self.interned_def_types.insert(val_def, merged);
        }
      }
    }
    Ok(())
  }

}
