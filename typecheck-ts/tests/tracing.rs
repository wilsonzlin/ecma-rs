use std::collections::HashMap;
use std::io;
use std::sync::{Arc, Mutex};
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::fmt::MakeWriter;

use typecheck_ts::{FileId, Host, HostError, Program};

#[derive(Default)]
struct MemoryHost {
  files: Mutex<HashMap<FileId, Arc<str>>>,
}

impl MemoryHost {
  fn insert(&self, id: FileId, src: &str) {
    self
      .files
      .lock()
      .unwrap()
      .insert(id, Arc::from(src.to_string()));
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .lock()
      .unwrap()
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new("missing file"))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

#[derive(Clone, Default)]
struct SharedWriter {
  buffer: Arc<Mutex<Vec<u8>>>,
}

impl SharedWriter {
  fn into_inner(self) -> Vec<u8> {
    match Arc::try_unwrap(self.buffer) {
      Ok(buffer) => buffer.into_inner().unwrap(),
      Err(arc) => arc.lock().unwrap().clone(),
    }
  }
}

struct SharedWriterGuard<'a> {
  buffer: &'a Arc<Mutex<Vec<u8>>>,
}

impl<'a> io::Write for SharedWriterGuard<'a> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    self.buffer.lock().unwrap().extend_from_slice(buf);
    Ok(buf.len())
  }

  fn flush(&mut self) -> io::Result<()> {
    Ok(())
  }
}

impl<'a> MakeWriter<'a> for SharedWriter {
  type Writer = SharedWriterGuard<'a>;

  fn make_writer(&'a self) -> Self::Writer {
    SharedWriterGuard {
      buffer: &self.buffer,
    }
  }
}

#[test]
fn tracing_emits_query_spans() {
  let writer = SharedWriter::default();
  let subscriber = tracing_subscriber::fmt()
    .with_span_events(FmtSpan::CLOSE)
    .with_max_level(tracing::Level::DEBUG)
    .with_ansi(false)
    .with_writer(writer.clone())
    .finish();
  let _guard = tracing::subscriber::set_default(subscriber);

  let host = MemoryHost::default();
  host.insert(FileId(0), "export const value = 1;");
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty());

  drop(_guard);
  let output = String::from_utf8(writer.into_inner()).unwrap();
  assert!(
    output.contains("typecheck_ts.check_body"),
    "expected check_body span output, got: {output}"
  );
  assert!(
    output.contains("duration_ms"),
    "expected duration_ms field to be recorded"
  );
}
