use crate::{DefId, FileId, TypeId};
use diagnostics::TextRange;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Public symbol identifier exposed through [`Program::symbol_at`] and
/// `global_bindings` helpers. This mirrors `semantic-js`'s [`SymbolId`] and
/// keeps the full 64-bit range to avoid truncation or collisions.
pub mod semantic_js {
  /// Opaque symbol identifier.
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
  pub struct SymbolId(pub u64);

  impl From<::semantic_js::ts::SymbolId> for SymbolId {
    fn from(id: ::semantic_js::ts::SymbolId) -> Self {
      SymbolId(id.0)
    }
  }

  impl From<SymbolId> for ::semantic_js::ts::SymbolId {
    fn from(id: SymbolId) -> Self {
      ::semantic_js::ts::SymbolId(id.0)
    }
  }
}

/// Recorded occurrence of a symbol within a span.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolOccurrence {
  pub range: TextRange,
  pub symbol: semantic_js::SymbolId,
}

/// Binding metadata for a symbol, including its canonical `semantic-js` symbol
/// identifier, optional backing definition, and optional type.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct SymbolBinding {
  pub symbol: semantic_js::SymbolId,
  pub def: Option<DefId>,
  pub type_id: Option<TypeId>,
}

/// Symbol metadata exposed via [`Program::symbol_info`].
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct SymbolInfo {
  pub symbol: semantic_js::SymbolId,
  pub def: Option<DefId>,
  pub file: Option<FileId>,
  pub type_id: Option<TypeId>,
  pub name: Option<String>,
  pub span: Option<TextRange>,
}
