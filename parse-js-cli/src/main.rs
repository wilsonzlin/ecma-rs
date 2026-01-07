use clap::Parser;
use diagnostics::render::{render_diagnostic_with_options, RenderOptions, SourceProvider};
use diagnostics::{host_error, Diagnostic, FileId, Span, TextRange};
use parse_js::{parse_with_options, parse_with_options_cancellable, ParseOptions};
use serde::Serialize;
use std::io::stdin;
use std::io::stdout;
use std::io::IsTerminal;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::exit;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc};
use std::time::Duration;

const SCHEMA_VERSION: u32 = 1;

#[derive(clap::ValueEnum, Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "lowercase")]
enum DialectFlag {
  Js,
  Jsx,
  Ts,
  Tsx,
  Dts,
}

impl From<DialectFlag> for parse_js::Dialect {
  fn from(value: DialectFlag) -> Self {
    match value {
      DialectFlag::Js => parse_js::Dialect::Js,
      DialectFlag::Jsx => parse_js::Dialect::Jsx,
      DialectFlag::Ts => parse_js::Dialect::Ts,
      DialectFlag::Tsx => parse_js::Dialect::Tsx,
      DialectFlag::Dts => parse_js::Dialect::Dts,
    }
  }
}

#[derive(clap::ValueEnum, Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "lowercase")]
enum SourceTypeFlag {
  Module,
  Script,
}

impl From<SourceTypeFlag> for parse_js::SourceType {
  fn from(value: SourceTypeFlag) -> Self {
    match value {
      SourceTypeFlag::Module => parse_js::SourceType::Module,
      SourceTypeFlag::Script => parse_js::SourceType::Script,
    }
  }
}

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {
  /// Read input from a file instead of stdin.
  #[arg(long, value_name = "PATH", conflicts_with = "path")]
  input: Option<PathBuf>,

  /// Read input from a file instead of stdin.
  #[arg(value_name = "PATH")]
  path: Option<PathBuf>,

  /// Parse the input using a specific dialect.
  #[arg(long, value_enum, value_name = "js|jsx|ts|tsx|dts")]
  dialect: Option<DialectFlag>,

  /// Parse the input as a module (default) or script.
  #[arg(long, value_enum, value_name = "module|script")]
  source_type: Option<SourceTypeFlag>,

  /// Emit JSON diagnostics on failure instead of human-readable diagnostics.
  #[arg(long)]
  json_errors: bool,

  /// Cancel parsing if it takes longer than this many seconds.
  #[arg(long, value_name = "SECS")]
  timeout_secs: Option<u64>,

  /// Force-enable ANSI colors in diagnostics output.
  #[arg(long)]
  color: bool,

  /// Disable ANSI colors in diagnostics output.
  #[arg(long)]
  no_color: bool,
}

struct SingleSource {
  name: String,
  text: Option<String>,
}

impl SourceProvider for SingleSource {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some(&self.name)
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    self.text.as_deref()
  }
}

#[derive(Clone, Copy)]
struct ErrorOutput {
  json: bool,
  render: RenderOptions,
}

#[derive(Serialize)]
struct JsonDiagnosticsOutput {
  schema_version: u32,
  diagnostics: Vec<Diagnostic>,
}

fn exit_with_diagnostic(
  source: &dyn SourceProvider,
  diagnostic: Diagnostic,
  output: ErrorOutput,
) -> ! {
  if output.json {
    let mut diagnostics = vec![diagnostic];
    diagnostics::sort_diagnostics(&mut diagnostics);
    let payload = JsonDiagnosticsOutput {
      schema_version: SCHEMA_VERSION,
      diagnostics,
    };
    if serde_json::to_writer(stdout(), &payload).is_err() {
      eprintln!(
        "{}",
        render_diagnostic_with_options(source, &payload.diagnostics[0], output.render)
      );
    }
    exit(1);
  }

  eprintln!("{}", render_diagnostic_with_options(source, &diagnostic, output.render));
  exit(1);
}

#[derive(Serialize)]
struct ParseOptionsOutput {
  dialect: DialectFlag,
  source_type: SourceTypeFlag,
}

#[derive(Serialize)]
struct ParseOutput<T> {
  schema_version: u32,
  options: ParseOptionsOutput,
  ast: T,
}

fn infer_dialect(path: &Path) -> Option<DialectFlag> {
  let file_name = path.file_name()?.to_string_lossy();
  if file_name.ends_with(".d.ts") {
    return Some(DialectFlag::Dts);
  }
  match path.extension()?.to_string_lossy().as_ref() {
    "js" => Some(DialectFlag::Js),
    "jsx" => Some(DialectFlag::Jsx),
    "ts" => Some(DialectFlag::Ts),
    "tsx" => Some(DialectFlag::Tsx),
    _ => None,
  }
}

fn main() {
  let args = Cli::parse();
  let color = if args.color {
    true
  } else if args.no_color {
    false
  } else {
    std::io::stderr().is_terminal()
  };
  let output = ErrorOutput {
    json: args.json_errors,
    render: RenderOptions {
      context_lines: 1,
      color,
      ..RenderOptions::default()
    },
  };
  let file = FileId(0);

  let input_path = args.input.as_ref().or(args.path.as_ref());
  let dialect = args
    .dialect
    .or_else(|| input_path.and_then(|path| infer_dialect(path)))
    .unwrap_or(DialectFlag::Ts);
  let source_type = args.source_type.unwrap_or(SourceTypeFlag::Module);
  let parse_options = ParseOptions {
    dialect: dialect.into(),
    source_type: source_type.into(),
  };

  let (source_name, raw) = match input_path {
    Some(path) => {
      let name = path.to_string_lossy().into_owned();
      match std::fs::read(path) {
        Ok(raw) => (name, raw),
        Err(err) => {
          let diagnostic = host_error(
            Some(Span::new(file, TextRange::new(0, 0))),
            format!("failed to read {name}: {err}"),
          );
          let provider = SingleSource {
            name,
            text: None,
          };
          exit_with_diagnostic(&provider, diagnostic, output);
        }
      }
    }
    None => {
      let name = "<stdin>".to_string();
      let mut raw = Vec::new();
      if let Err(err) = stdin().read_to_end(&mut raw) {
        let diagnostic = host_error(
          Some(Span::new(file, TextRange::new(0, 0))),
          format!("failed to read from stdin: {err}"),
        );
        let provider = SingleSource {
          name,
          text: None,
        };
        exit_with_diagnostic(&provider, diagnostic, output);
      }
      (name, raw)
    }
  };

  let source = match String::from_utf8(raw) {
    Ok(text) => text,
    Err(err) => {
      let message = if input_path.is_some() {
        format!("{source_name} is not valid UTF-8: {err}")
      } else {
        format!("stdin is not valid UTF-8: {err}")
      };
      let diagnostic = host_error(Some(Span::new(file, TextRange::new(0, 0))), message);
      let provider = SingleSource {
        name: source_name,
        text: None,
      };
      exit_with_diagnostic(&provider, diagnostic, output);
    }
  };

  let provider = SingleSource {
    name: source_name,
    text: Some(source),
  };
  let source = provider.text.as_deref().unwrap();

  let parsed = match args.timeout_secs {
    Some(secs) => {
      let cancel = Arc::new(AtomicBool::new(false));
      let timeout = Duration::from_secs(secs);
      let (done_tx, done_rx) = mpsc::channel::<()>();

      let timeout_thread = if timeout.is_zero() {
        cancel.store(true, Ordering::Relaxed);
        None
      } else {
        let cancel = Arc::clone(&cancel);
        Some(std::thread::spawn(move || {
          if matches!(
            done_rx.recv_timeout(timeout),
            Err(mpsc::RecvTimeoutError::Timeout)
          ) {
            cancel.store(true, Ordering::Relaxed);
          }
        }))
      };

      let parsed = match parse_with_options_cancellable(source, parse_options, Arc::clone(&cancel)) {
        Ok(parsed) => parsed,
        Err(err) => {
          let mut diagnostic = err.to_diagnostic(file);
          if err.typ == parse_js::error::SyntaxErrorType::Cancelled {
            diagnostic = diagnostic.with_note(format!("timed out after {secs} seconds"));
          }
          exit_with_diagnostic(&provider, diagnostic, output);
        }
      };

      let _ = done_tx.send(());
      if let Some(handle) = timeout_thread {
        let _ = handle.join();
      }
      parsed
    }
    None => match parse_with_options(source, parse_options) {
      Ok(parsed) => parsed,
      Err(err) => {
        let diagnostic = err.to_diagnostic(file);
        exit_with_diagnostic(&provider, diagnostic, output);
      }
    },
  };

  let payload = ParseOutput {
    schema_version: SCHEMA_VERSION,
    options: ParseOptionsOutput {
      dialect,
      source_type,
    },
    ast: parsed,
  };

  if let Err(err) = serde_json::to_writer(stdout(), &payload) {
    let diagnostic = host_error(
      Some(Span::new(file, TextRange::new(0, 0))),
      format!("failed to write output: {err}"),
    );
    exit_with_diagnostic(&provider, diagnostic, output);
  }
}
