use clap::Parser;
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{diagnostic_from_syntax_error, host_error, Diagnostic, FileId, Span, TextRange};
use parse_js::parse;
use std::io::stdin;
use std::io::stdout;
use std::io::Read;
use std::process::exit;

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {}

struct StdinSource {
  text: String,
}

impl SourceProvider for StdinSource {
  fn file_name(&self, _file: FileId) -> &str {
    "<stdin>"
  }

  fn file_text(&self, _file: FileId) -> &str {
    &self.text
  }
}

fn exit_with_diagnostic(source: &StdinSource, diagnostic: Diagnostic) -> ! {
  eprintln!("{}", render_diagnostic(source, &diagnostic));
  exit(1);
}

fn main() {
  let _args = Cli::parse();
  let file = FileId(0);

  let mut source = String::new();
  if let Err(err) = stdin().read_to_string(&mut source) {
    let diagnostic = host_error(
      Some(Span::new(file, TextRange::new(0, 0))),
      format!("failed to read from stdin: {err}"),
    );
    let provider = StdinSource {
      text: String::new(),
    };
    exit_with_diagnostic(&provider, diagnostic);
  }

  let provider = StdinSource {
    text: source.clone(),
  };

  let parsed = match parse(&source) {
    Ok(parsed) => parsed,
    Err(err) => {
      let diagnostic = diagnostic_from_syntax_error(file, &err);
      exit_with_diagnostic(&provider, diagnostic);
    }
  };

  if let Err(err) = serde_json::to_writer(stdout(), &parsed) {
    let diagnostic = host_error(
      Some(Span::new(file, TextRange::new(0, 0))),
      format!("failed to write output: {err}"),
    );
    exit_with_diagnostic(&provider, diagnostic);
  }
}
