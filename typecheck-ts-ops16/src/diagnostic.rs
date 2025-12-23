#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
  pub message: String,
  pub notes: Vec<String>,
}

impl Diagnostic {
  pub fn new(message: impl Into<String>) -> Self {
    Diagnostic {
      message: message.into(),
      notes: Vec::new(),
    }
  }

  pub fn with_note(mut self, note: impl Into<String>) -> Self {
    self.notes.push(note.into());
    self
  }
}
