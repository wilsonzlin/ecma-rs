use diagnostics_h19::Diagnostic;
use diagnostics_h19::Span;
use parse_js;
use std::collections::HashMap;
use std::sync::Arc;

pub type FileId = usize;

#[derive(Debug, Clone)]
pub struct CheckReport {
  pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, thiserror::Error)]
pub enum HostError {
  #[error("file {0} not found")]
  MissingFile(FileId),
  #[error("failed to read file {0}: {1}")]
  ReadFailed(FileId, String),
}

#[derive(Debug, thiserror::Error)]
pub enum CheckError {
  #[error(transparent)]
  Host(#[from] HostError),
}

pub trait Host {
  fn files(&self) -> Vec<FileId>;
  fn file_name(&self, file_id: FileId) -> Option<&str>;
  fn file_text(&self, file_id: FileId) -> Result<Arc<str>, HostError>;
  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId>;
}

#[derive(Debug, Clone)]
pub struct InMemoryFile {
  pub name: String,
  pub text: String,
}

#[derive(Debug, Default)]
pub struct InMemoryHost {
  files: Vec<InMemoryFile>,
  name_to_id: HashMap<String, FileId>,
}

impl InMemoryHost {
  pub fn new(files: Vec<InMemoryFile>) -> Self {
    let mut name_to_id = HashMap::new();
    for (idx, file) in files.iter().enumerate() {
      name_to_id.insert(file.name.clone(), idx);
    }

    Self { files, name_to_id }
  }
}

impl Host for InMemoryHost {
  fn files(&self) -> Vec<FileId> {
    (0..self.files.len()).collect()
  }

  fn file_name(&self, file_id: FileId) -> Option<&str> {
    self.files.get(file_id).map(|f| f.name.as_str())
  }

  fn file_text(&self, file_id: FileId) -> Result<Arc<str>, HostError> {
    let file = self
      .files
      .get(file_id)
      .ok_or(HostError::MissingFile(file_id))?;
    Ok(Arc::from(file.text.as_str()))
  }

  fn resolve(&self, _from: FileId, specifier: &str) -> Option<FileId> {
    self.name_to_id.get(specifier).copied()
  }
}

pub fn check_program(host: &impl Host) -> Result<CheckReport, CheckError> {
  let mut files = host.files();
  files.sort_by(|a, b| host.file_name(*a).cmp(&host.file_name(*b)));

  let mut diagnostics = Vec::new();

  for file_id in files {
    let source = host.file_text(file_id)?;

    match parse_js::parse(&source) {
      Ok(_) => {}
      Err(err) => {
        let span = Span {
          file: file_id as u32,
          start: err.loc.0 as u32,
          end: err.loc.1 as u32,
        };

        diagnostics.push(Diagnostic::new("PARSE", format!("{}", err), Some(span)));
      }
    }

    if diagnostics.len() > 10_000 {
      // Avoid runaway diagnostics in degenerate cases.
      break;
    }
  }

  Ok(CheckReport { diagnostics })
}
