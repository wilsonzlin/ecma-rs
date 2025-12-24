use clap::builder::PossibleValuesParser;
use clap::builder::TypedValueParser;
use clap::Parser;
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{FileId, Severity};
use minify_js::minify;
use minify_js::TopLevelMode;
use std::fs::File;
use std::io::stdin;
use std::io::stdout;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;
use std::process;

#[derive(Parser)]
#[command(name = "minify-js", about = "Extremely fast JS minifier")]
// WARNING: Keep descriptions in sync with Cfg.
struct Cli {
  /// File to minify; omit for stdin.
  #[arg(short, long)]
  input: Option<PathBuf>,

  /// Output destination; omit for stdout.
  #[arg(short, long)]
  output: Option<PathBuf>,

  /// Whether file is a module or global script.
  #[arg(
    short,
    long,
    value_parser = PossibleValuesParser::new(["global", "module"])
        .map(|s| match s.as_str() {
          "global" => TopLevelMode::Global,
          "module" => TopLevelMode::Module,
          _ => unreachable!(),
        }),
  )]
  mode: TopLevelMode,
}

struct SingleFileSource<'a> {
  name: String,
  text: &'a str,
}

impl<'a> SourceProvider for SingleFileSource<'a> {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some(&self.name)
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    Some(self.text)
  }
}

fn main() {
  let args = Cli::parse();
  let input_name = args
    .input
    .as_ref()
    .map(|p| p.to_string_lossy().into_owned())
    .unwrap_or_else(|| "<stdin>".to_string());
  let mut input = Vec::new();
  let mut input_file: Box<dyn Read> = match args.input.as_ref() {
    Some(p) => match File::open(p) {
      Ok(f) => Box::new(f),
      Err(err) => {
        eprintln!("error: failed to open {}: {err}", p.display());
        process::exit(1);
      }
    },
    None => Box::new(stdin()),
  };
  if let Err(err) = input_file.read_to_end(&mut input) {
    eprintln!("error: failed to read input: {err}");
    process::exit(1);
  }
  let source = match std::str::from_utf8(&input) {
    Ok(source) => source,
    Err(err) => {
      eprintln!("error: input is not valid UTF-8: {err}");
      process::exit(1);
    }
  };
  let mut output = Vec::new();
  match minify(args.mode, source, &mut output) {
    Ok(()) => {
      let write_result = match args.output.as_ref() {
        Some(p) => File::create(p).and_then(|mut file| file.write_all(&output)),
        None => stdout().write_all(&output),
      };
      if let Err(err) = write_result {
        eprintln!("error: failed to write output: {err}");
        process::exit(1);
      }
    }
    Err(diagnostics) => {
      let provider = SingleFileSource {
        name: input_name,
        text: source,
      };
      let mut exit_code = 0;
      for diagnostic in diagnostics {
        if diagnostic.severity == Severity::Error {
          exit_code = 1;
        }
        eprintln!("{}", render_diagnostic(&provider, &diagnostic));
      }
      process::exit(exit_code);
    }
  }
}
