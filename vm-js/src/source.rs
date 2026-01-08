use std::fmt::Display;
use std::sync::Arc;

/// Source text for scripts/modules with precomputed line starts.
#[derive(Debug, Clone)]
pub struct SourceText {
  pub name: Arc<str>,
  pub text: Arc<str>,
  line_starts: Vec<u32>,
}

impl SourceText {
  pub fn new(name: impl Into<Arc<str>>, text: impl Into<Arc<str>>) -> Self {
    let name = name.into();
    let text = text.into();
    let mut line_starts = vec![0u32];

    for (idx, ch) in text.char_indices() {
      if ch == '\n' {
        let next = (idx + 1).min(text.len());
        if let Ok(next) = u32::try_from(next) {
          line_starts.push(next);
        }
      }
    }

    Self {
      name,
      text,
      line_starts,
    }
  }

  /// Convert a UTF-8 byte offset into 1-based `(line, col)` numbers.
  ///
  /// Offsets that fall outside the text are clamped; offsets that fall inside a
  /// UTF-8 sequence are clamped backwards to the nearest valid char boundary.
  pub fn line_col(&self, offset: u32) -> (u32, u32) {
    let mut offset = offset as usize;
    offset = offset.min(self.text.len());
    while offset > 0 && !self.text.is_char_boundary(offset) {
      offset -= 1;
    }

    let offset_u32 = u32::try_from(offset).unwrap_or(u32::MAX);
    let line_idx = match self.line_starts.binary_search(&offset_u32) {
      Ok(idx) => idx,
      Err(0) => 0,
      Err(idx) => idx - 1,
    };

    let line_start = *self
      .line_starts
      .get(line_idx)
      .unwrap_or(&u32::try_from(self.text.len()).unwrap_or(u32::MAX)) as usize;

    let slice = &self.text[line_start..offset];
    let col0 = slice.chars().count() as u32;
    (line_idx as u32 + 1, col0 + 1)
  }
}

/// A single stack frame for stack traces and termination errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackFrame {
  pub function: Option<Arc<str>>,
  pub source: Arc<str>,
  pub line: u32,
  pub col: u32,
}

impl Display for StackFrame {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match &self.function {
      Some(function) => write!(
        f,
        "at {function} ({source}:{line}:{col})",
        function = function,
        source = self.source,
        line = self.line,
        col = self.col
      ),
      None => write!(
        f,
        "at {source}:{line}:{col}",
        source = self.source,
        line = self.line,
        col = self.col
      ),
    }
  }
}

/// Format stack frames into a stable stack trace string.
pub fn format_stack_trace(frames: &[StackFrame]) -> String {
  frames
    .iter()
    .map(ToString::to_string)
    .collect::<Vec<_>>()
    .join("\n")
}

