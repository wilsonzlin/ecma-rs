use super::*;

impl Program {
  /// Return symbol at a given file offset, if any.
  pub fn symbol_at(&self, file: FileId, offset: u32) -> Option<semantic_js::SymbolId> {
    match self.symbol_at_fallible(file, offset) {
      Ok(symbol) => symbol,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn symbol_at_fallible(
    &self,
    file: FileId,
    offset: u32,
  ) -> Result<Option<semantic_js::SymbolId>, FatalError> {
    self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(occurrences) = state.symbol_occurrences.get(&file) {
          return Ok(Self::symbol_from_occurrences(occurrences, offset));
        }
      }
      let occurrences = crate::db::symbol_occurrences(&state.typecheck_db, file);
      Ok(Self::symbol_from_occurrences(&occurrences, offset))
    })
  }

  fn symbol_from_occurrences(
    occurrences: &[SymbolOccurrence],
    offset: u32,
  ) -> Option<semantic_js::SymbolId> {
    let pivot = occurrences.partition_point(|occ| occ.range.start <= offset);
    let mut best_containing: Option<(u32, u32, u32, semantic_js::SymbolId)> = None;
    let mut best_empty: Option<(u32, u32, u32, semantic_js::SymbolId)> = None;

    for occ in occurrences[..pivot].iter().rev() {
      let range = occ.range;
      let len = range.len();
      let key = (len, range.start, range.end, occ.symbol);
      if range.start <= offset && offset < range.end {
        if best_containing
          .map(|existing| key < existing)
          .unwrap_or(true)
        {
          best_containing = Some(key);
        }
      } else if range.start == range.end && range.start == offset {
        if best_empty.map(|existing| key < existing).unwrap_or(true) {
          best_empty = Some(key);
        }
      }
    }

    best_containing
      .or(best_empty)
      .map(|(_, _, _, symbol)| symbol)
  }

  /// Symbol metadata if available (def, file, type, name).
  pub fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    match self.with_analyzed_state(|state| Ok(state.symbol_info(symbol))) {
      Ok(info) => info,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Raw symbol occurrences for debugging.
  pub fn debug_symbol_occurrences(&self, file: FileId) -> Vec<(TextRange, semantic_js::SymbolId)> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(occurrences) = state.symbol_occurrences.get(&file) {
          return Ok(occurrences.clone());
        }
      }
      Ok(crate::db::symbol_occurrences(&state.typecheck_db, file).to_vec())
    }) {
      Ok(occurrences) => occurrences
        .iter()
        .map(|occ| (occ.range, occ.symbol))
        .collect(),
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }
}
