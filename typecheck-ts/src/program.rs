use crate::diagnostic::Diagnostic;
use crate::error::{BodyId, FatalError, FileId, HostError, Ice};
use std::any::Any;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

pub trait Host: Send + Sync {
  fn root_files(&self) -> Vec<FileId>;

  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError>;

  fn bodies_of(&self, file: FileId) -> Result<Vec<BodyId>, HostError>;

  fn check_body(
    &self,
    file: FileId,
    body: BodyId,
    diagnostics: &mut Vec<Diagnostic>,
  ) -> Result<(), FatalError>;
}

#[derive(Default, Debug)]
pub struct CheckReport {
  pub diagnostics: Vec<Diagnostic>,
  pub fatal_errors: Vec<FatalError>,
}

impl CheckReport {
  pub fn has_ice(&self) -> bool {
    self
      .fatal_errors
      .iter()
      .any(|error| matches!(error, FatalError::Ice(_)))
  }
}

pub struct Program<H: Host> {
  host: Arc<H>,
}

impl<H: Host> Program<H> {
  pub fn new(host: Arc<H>) -> Self {
    Self { host }
  }

  pub fn check(&self) -> CheckReport {
    let mut report = CheckReport::default();

    let root_files = match self.guard(&mut report, Vec::new(), |diagnostics| {
      let files = self.host.root_files();
      // Nothing to emit here yet, but keep the signature uniform.
      let _ = diagnostics;
      Ok(files)
    }) {
      Some(files) => files,
      None => return report,
    };

    for file in root_files {
      let file_context = vec![("file".to_string(), file.to_string())];

      let _text = match self.guard(&mut report, file_context.clone(), |diagnostics| {
        let _ = diagnostics;
        self.host.file_text(file).map_err(FatalError::Host)
      }) {
        Some(text) => text,
        None => continue,
      };

      let bodies = match self.guard(&mut report, file_context.clone(), |diagnostics| {
        let _ = diagnostics;
        self.host.bodies_of(file).map_err(FatalError::Host)
      }) {
        Some(bodies) => bodies,
        None => continue,
      };

      for body in bodies {
        let mut context = file_context.clone();
        context.push(("body".to_string(), body.to_string()));

        let _ = self.guard(&mut report, context, |diagnostics| {
          self.host.check_body(file, body, diagnostics)
        });
      }
    }

    report
  }

  fn guard<T, F>(&self, report: &mut CheckReport, context: Vec<(String, String)>, f: F) -> Option<T>
  where
    F: FnOnce(&mut Vec<Diagnostic>) -> Result<T, FatalError>,
  {
    let result = catch_unwind(AssertUnwindSafe(|| f(&mut report.diagnostics)));
    match result {
      Ok(Ok(value)) => Some(value),
      Ok(Err(fatal)) => {
        self.record_fatal(report, fatal, context);
        None
      }
      Err(panic) => {
        let message = panic_message(panic);
        let ice = Ice::new(message);
        self.record_fatal(report, FatalError::Ice(ice), context);
        None
      }
    }
  }

  fn record_fatal(
    &self,
    report: &mut CheckReport,
    fatal: FatalError,
    context: Vec<(String, String)>,
  ) {
    match &fatal {
      FatalError::Host(err) => {
        let mut diagnostic = Diagnostic::host(err);
        if !context.is_empty() {
          diagnostic.context.extend(context.clone());
          diagnostic
            .notes
            .extend(context.iter().map(|(k, v)| format!("context {k} = {v}")));
        }
        report.diagnostics.push(diagnostic);
        report.fatal_errors.push(fatal);
      }
      FatalError::Cancelled => {
        let mut diagnostic = Diagnostic::cancelled();
        if !context.is_empty() {
          diagnostic.context.extend(context.clone());
          diagnostic
            .notes
            .extend(context.iter().map(|(k, v)| format!("context {k} = {v}")));
        }
        report.diagnostics.push(diagnostic);
        report.fatal_errors.push(fatal);
      }
      FatalError::Ice(ice) => {
        let mut ice = ice.clone();
        ice.context.extend(context);
        let diagnostic = ice.to_diagnostic(capture_backtrace());
        report.fatal_errors.push(FatalError::Ice(ice.clone()));
        report.diagnostics.push(diagnostic);
      }
    }
  }
}

fn panic_message(payload: Box<dyn Any + Send>) -> String {
  if let Some(s) = payload.downcast_ref::<&str>() {
    s.to_string()
  } else if let Some(s) = payload.downcast_ref::<String>() {
    s.clone()
  } else {
    "panic occurred".to_string()
  }
}

fn capture_backtrace() -> Option<String> {
  #[cfg(feature = "capture-backtrace")]
  {
    use std::backtrace::Backtrace;
    Some(Backtrace::capture().to_string())
  }

  #[cfg(not(feature = "capture-backtrace"))]
  {
    None
  }
}
