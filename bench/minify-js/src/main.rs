use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use minify_js::minify;
use minify_js::TopLevelMode;
use std::any::Any;
use std::env;
use std::fs::File;
use std::io::Read;
use std::process;
use std::time::Instant;

struct SingleFileSource<'a> {
  name: &'a str,
  text: &'a str,
}

impl SourceProvider for SingleFileSource<'_> {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some(self.name)
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    Some(self.text)
  }
}

enum MinifyOutcome {
  Ok,
  Diagnostics(Vec<Diagnostic>),
}

trait IntoMinifyOutcome {
  fn into_outcome(self, file: FileId) -> MinifyOutcome;
}

impl IntoMinifyOutcome for Vec<Diagnostic> {
  fn into_outcome(self, _file: FileId) -> MinifyOutcome {
    diagnostics_outcome(self)
  }
}

impl<E> IntoMinifyOutcome for Result<(), E>
where
  E: 'static + std::fmt::Debug,
{
  fn into_outcome(self, file: FileId) -> MinifyOutcome {
    match self {
      Ok(()) => MinifyOutcome::Ok,
      Err(err) => MinifyOutcome::Diagnostics(fallback_diagnostics(err, file)),
    }
  }
}

impl<E> IntoMinifyOutcome for Result<Vec<Diagnostic>, E>
where
  E: 'static + std::fmt::Debug,
{
  fn into_outcome(self, file: FileId) -> MinifyOutcome {
    match self {
      Ok(diagnostics) => diagnostics_outcome(diagnostics),
      Err(err) => MinifyOutcome::Diagnostics(fallback_diagnostics(err, file)),
    }
  }
}

fn diagnostics_outcome(diagnostics: Vec<Diagnostic>) -> MinifyOutcome {
  if diagnostics.is_empty() {
    MinifyOutcome::Ok
  } else {
    MinifyOutcome::Diagnostics(diagnostics)
  }
}

fn fallback_diagnostics<E>(err: E, file: FileId) -> Vec<Diagnostic>
where
  E: 'static + std::fmt::Debug,
{
  if let Some(diagnostics) = (&err as &dyn Any).downcast_ref::<Vec<Diagnostic>>() {
    return diagnostics.clone();
  }

  vec![Diagnostic::error(
    "MINIFY0000",
    format!("{err:?}"),
    Span {
      file,
      range: TextRange::new(0, 0),
    },
  )]
}

fn main() {
  let args: Vec<String> = env::args().collect();
  let mut code = Vec::new();
  File::open(&args[1])
    .expect("open file")
    .read_to_end(&mut code)
    .expect("read file");
  let src_str = std::str::from_utf8(&code).expect("input must be valid UTF-8");

  let iterations = u64::from_str_radix(&args[2], 10).expect("parse iterations argument");
  let mut output_len = 0;
  let mut output = Vec::new();
  let file = FileId(0);
  let source = SingleFileSource {
    name: &args[1],
    text: src_str,
  };
  let started = Instant::now();
  for _ in 0..iterations {
    output.clear();
    match minify(TopLevelMode::Global, src_str, &mut output).into_outcome(file) {
      MinifyOutcome::Ok => {
        output_len = output.len();
      }
      MinifyOutcome::Diagnostics(diagnostics) => {
        for diagnostic in diagnostics {
          eprint!("{}", render_diagnostic(&source, &diagnostic));
        }
        process::exit(1);
      }
    }
  }
  let elapsed_ns = started.elapsed().as_nanos();

  println!("{} {}", output_len, elapsed_ns);
}
