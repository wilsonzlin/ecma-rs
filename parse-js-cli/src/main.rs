use clap::Parser;
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{diagnostic_from_syntax_error, FileId};
use parse_js::parse;
use std::io::stdin;
use std::io::stdout;
use std::io::Read;
use std::process::exit;

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {}

struct StdinSource<'a> {
  text: &'a str,
}

impl SourceProvider for StdinSource<'_> {
  fn file_name(&self, _file: FileId) -> &str {
    "<stdin>"
  }

  fn file_text(&self, _file: FileId) -> &str {
    self.text
  }
}

fn main() {
  let _args = Cli::parse();
  let mut source = String::new();
  stdin()
    .read_to_string(&mut source)
    .expect("read from stdin");
  match parse(&source) {
    Ok(parsed) => serde_json::to_writer(stdout(), &parsed).expect("write to stdout"),
    Err(err) => {
      let diagnostic = diagnostic_from_syntax_error(FileId(0), &err);
      let rendered = render_diagnostic(&StdinSource { text: &source }, &diagnostic);
      eprint!("{rendered}");
      exit(1);
    }
  }
}
