use clap::Parser;
use parse_js::parse;
use std::io::stdin;
use std::io::stdout;
use std::io::Read;

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {}

fn main() {
  let args = Cli::parse();
  let mut source = Vec::new();
  stdin().read_to_end(&mut source).expect("read from stdin");
  let source_str = std::str::from_utf8(&source).expect("valid UTF-8");
  let parsed = parse(source_str).expect("parse");
  serde_json::to_writer(stdout(), &parsed).expect("write to stdout");
}
