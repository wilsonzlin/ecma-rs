use super::*;

impl ProgramState {
  pub(super) fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    let binding = self
      .global_bindings
      .iter()
      .find(|(_, binding)| binding.symbol == symbol);

    let resolve_def_type = |def_id: DefId| self.interned_def_types.get(&def_id).copied();

    let mut def = self
      .symbol_to_def
      .get(&symbol)
      .copied()
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.def));
    let mut file = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.file));
    let mut span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));
    let mut name = def
      .and_then(|def_id| self.def_data.get(&def_id).map(|data| data.name.clone()))
      .or_else(|| binding.as_ref().map(|(name, _)| name.to_string()));
    let mut type_id = def
      .and_then(resolve_def_type)
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.type_id));

    if def.is_none() {
      if let Some(semantics) = self.semantics.as_ref() {
        let sem_symbol: sem_ts::SymbolId = symbol.into();
        if let Some(sym_data) = semantics.symbols().symbol_opt(sem_symbol) {
          for ns in [
            sem_ts::Namespace::VALUE,
            sem_ts::Namespace::TYPE,
            sem_ts::Namespace::NAMESPACE,
          ] {
            if !sym_data.namespaces.contains(ns) {
              continue;
            }
            if let Some(decl_id) = semantics.symbol_decls(sem_symbol, ns).first() {
              let decl = semantics.symbols().decl(*decl_id);
              def = Some(decl.def_id);
              file = Some(decl.file);
              if name.is_none() {
                name = Some(sym_data.name.clone());
              }
              if type_id.is_none() {
                type_id = resolve_def_type(decl.def_id);
              }
              break;
            }
          }
        }
      }
    }

    if span.is_none() {
      span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));
    }

    if def.is_none() && type_id.is_none() && name.is_none() && file.is_none() {
      if self.snapshot_loaded {
        if let Some(local) = self.local_symbol_info.get(&symbol) {
          return Some(SymbolInfo {
            symbol,
            def: None,
            file: Some(local.file),
            type_id: None,
            name: Some(local.name.clone()),
            span: local.span,
          });
        }
      }
      let mut files: Vec<_> = self.file_kinds.keys().copied().collect();
      files.sort_by_key(|file| file.0);
      for file in files {
        let locals = crate::db::local_symbol_info(&self.typecheck_db, file);
        if let Some(local) = locals.get(&symbol) {
          return Some(SymbolInfo {
            symbol,
            def: None,
            file: Some(local.file),
            type_id: None,
            name: Some(local.name.clone()),
            span: local.span,
          });
        }
      }
      return None;
    }
    if name.is_none() {
      name = binding.as_ref().map(|(name, _)| name.to_string());
    }

    Some(SymbolInfo {
      symbol,
      def,
      file,
      type_id,
      name,
      span,
    })
  }

  pub(super) fn expr_at(&mut self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    if self.snapshot_loaded {
      if self.body_results.is_empty() {
        return None;
      }

      let mut best_containing: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, ExprId),
        (BodyId, ExprId, TextRange),
      )> = None;
      let mut best_empty: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, ExprId),
        (BodyId, ExprId, TextRange),
      )> = None;

      for (body_id, result) in self.body_results.iter() {
        let Some(meta) = self.body_map.get(body_id) else {
          continue;
        };
        if meta.file != file {
          continue;
        }
        let Some((expr_id, _)) = result.expr_at(offset) else {
          continue;
        };
        let Some(span) = result.expr_span(expr_id) else {
          continue;
        };

        let Some(body_span) = body_extent_from_spans(result.expr_spans(), result.pat_spans())
        else {
          continue;
        };
        let key = (
          span.len(),
          span.start,
          span.end,
          body_span.len(),
          body_span.start,
          body_span.end,
          *body_id,
          expr_id,
        );

        if span.start <= offset && offset < span.end {
          if best_containing
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_containing = Some((key, (*body_id, expr_id, span)));
          }
        } else if span.is_empty() && span.start == offset {
          if best_empty
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_empty = Some((key, (*body_id, expr_id, span)));
          }
        }
      }

      return match (best_containing, best_empty) {
        (
          Some((_, (cont_body, cont_expr, cont_span))),
          Some((_, (empty_body, empty_expr, empty_span))),
        ) => {
          if empty_span.start > cont_span.start && empty_span.end < cont_span.end {
            Some((empty_body, empty_expr))
          } else {
            Some((cont_body, cont_expr))
          }
        }
        (Some((_, (body, expr, _))), None) => Some((body, expr)),
        (None, Some((_, (body, expr, _)))) => Some((body, expr)),
        (None, None) => None,
      };
    }

    db::expr_at(&self.typecheck_db, file, offset)
  }

  pub(super) fn pat_at(&mut self, file: FileId, offset: u32) -> Option<(BodyId, PatId)> {
    if self.snapshot_loaded {
      let mut best_containing: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, PatId),
        (BodyId, PatId, TextRange),
      )> = None;
      let mut best_empty: Option<(
        (u32, u32, u32, u32, u32, u32, BodyId, PatId),
        (BodyId, PatId, TextRange),
      )> = None;

      for (body_id, result) in self.body_results.iter() {
        let Some(meta) = self.body_map.get(body_id) else {
          continue;
        };
        if meta.file != file {
          continue;
        }
        let Some((pat_id, span)) = expr_at_from_spans(result.pat_spans(), offset) else {
          continue;
        };
        let pat_id = PatId(pat_id.0);
        let Some(body_span) = body_extent_from_spans(result.expr_spans(), result.pat_spans())
        else {
          continue;
        };
        let key = (
          span.len(),
          span.start,
          span.end,
          body_span.len(),
          body_span.start,
          body_span.end,
          *body_id,
          pat_id,
        );

        if span.start <= offset && offset < span.end {
          if best_containing
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_containing = Some((key, (*body_id, pat_id, span)));
          }
        } else if span.is_empty() && span.start == offset {
          if best_empty
            .as_ref()
            .map(|(existing, _)| key < *existing)
            .unwrap_or(true)
          {
            best_empty = Some((key, (*body_id, pat_id, span)));
          }
        }
      }

      match (best_containing, best_empty) {
        (
          Some((_, (cont_body, cont_pat, cont_span))),
          Some((_, (empty_body, empty_pat, empty_span))),
        ) => {
          if empty_span.start > cont_span.start && empty_span.end < cont_span.end {
            return Some((empty_body, empty_pat));
          }
          return Some((cont_body, cont_pat));
        }
        (Some((_, (body, pat, _))), None) => return Some((body, pat)),
        (None, Some((_, (body, pat, _)))) => return Some((body, pat)),
        (None, None) => return None,
      }
    }

    db::file_span_index(&self.typecheck_db, file)
      .pat_at(offset)
      .map(|res| res.id)
  }

  pub(super) fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    self.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => {
        if var.body != MISSING_BODY {
          Some(var.body)
        } else {
          self.var_initializer(def).map(|init| init.body)
        }
      }
      DefKind::VarDeclarator(var) => var.body,
      DefKind::Class(class) => class.body,
      DefKind::Enum(en) => en.body,
      DefKind::Namespace(ns) => ns.body,
      DefKind::Module(ns) => ns.body,
      DefKind::Import(_) | DefKind::ImportAlias(_) => None,
      DefKind::Interface(_) => None,
      DefKind::TypeAlias(_) => None,
    })
  }

  pub(super) fn owner_of_body(&self, body: BodyId) -> Option<DefId> {
    self.body_owners.get(&body).copied()
  }
}
