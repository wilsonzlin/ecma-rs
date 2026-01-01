use clap::Parser;
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{host_error, Diagnostic, FileId, Span, TextRange};
use parse_js::{parse, parse_with_options_cancellable, ParseOptions};
use std::io::stdin;
use std::io::stdout;
use std::io::Read;
use std::process::exit;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc};
use std::time::Duration;

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {
  /// Cancel parsing if it takes longer than this many seconds.
  #[arg(long, value_name = "SECS")]
  timeout_secs: Option<u64>,
}

struct StdinSource {
  text: String,
}

impl SourceProvider for StdinSource {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some("<stdin>")
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    Some(&self.text)
  }
}

fn exit_with_diagnostic(source: &StdinSource, diagnostic: Diagnostic) -> ! {
  eprintln!("{}", render_diagnostic(source, &diagnostic));
  exit(1);
}

fn main() {
  let args = Cli::parse();
  let file = FileId(0);

  let mut raw = Vec::new();
  if let Err(err) = stdin().read_to_end(&mut raw) {
    let diagnostic = host_error(
      Some(Span::new(file, TextRange::new(0, 0))),
      format!("failed to read from stdin: {err}"),
    );
    let provider = StdinSource {
      text: String::new(),
    };
    exit_with_diagnostic(&provider, diagnostic);
  }

  let source = match String::from_utf8(raw) {
    Ok(text) => text,
    Err(err) => {
      let diagnostic = host_error(
        Some(Span::new(file, TextRange::new(0, 0))),
        format!("stdin is not valid UTF-8: {err}"),
      );
      let provider = StdinSource {
        text: String::new(),
      };
      exit_with_diagnostic(&provider, diagnostic);
    }
  };

  let provider = StdinSource {
    text: source.clone(),
  };

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
          if matches!(done_rx.recv_timeout(timeout), Err(mpsc::RecvTimeoutError::Timeout)) {
            cancel.store(true, Ordering::Relaxed);
          }
        }))
      };

      let parsed = match parse_with_options_cancellable(
        &source,
        ParseOptions::default(),
        Arc::clone(&cancel),
      ) {
        Ok(parsed) => parsed,
        Err(err) => {
          let mut diagnostic = err.to_diagnostic(file);
          if err.typ == parse_js::error::SyntaxErrorType::Cancelled {
            diagnostic = diagnostic.with_note(format!("timed out after {secs} seconds"));
          }
          exit_with_diagnostic(&provider, diagnostic);
        }
      };

      let _ = done_tx.send(());
      if let Some(handle) = timeout_thread {
        let _ = handle.join();
      }
      parsed
    }
    None => match parse(&source) {
      Ok(parsed) => parsed,
      Err(err) => {
        let diagnostic = err.to_diagnostic(file);
        exit_with_diagnostic(&provider, diagnostic);
      }
    },
  };

  if let Err(err) = serde_json::to_writer(stdout(), &parsed) {
    let diagnostic = host_error(
      Some(Span::new(file, TextRange::new(0, 0))),
      format!("failed to write output: {err}"),
    );
    exit_with_diagnostic(&provider, diagnostic);
  }
}
