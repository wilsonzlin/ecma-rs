use clap::builder::PossibleValuesParser;
use clap::builder::TypedValueParser;
use clap::Parser;
use minify_js::minify;
use minify_js::Session;
use minify_js::TopLevelMode;
use std::fs::File;
use std::io::stdin;
use std::io::stdout;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;

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

fn main() {
  let args = Cli::parse();
  let mut input = Vec::new();
  let mut input_file: Box<dyn Read> = match args.input {
    Some(p) => Box::new(File::open(p).expect("open input file")),
    None => Box::new(stdin()),
  };
  input_file.read_to_end(&mut input).expect("read input");
  let input = String::from_utf8(input).expect("input must be valid UTF-8");
  let mut output = Vec::new();
  let session = Session::new();
  minify(&session, args.mode, &input, &mut output).expect("minify");
  match args.output {
    Some(p) => File::create(p)
      .expect("open output file")
      .write_all(&output),
    None => stdout().write_all(&output),
  }
  .expect("write output");
}
