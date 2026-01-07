use clap::builder::PossibleValuesParser;
use clap::builder::TypedValueParser;
use clap::{ArgAction, Parser, ValueEnum};
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{host_error, FileId, Severity, Span, TextRange};
use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode, TsEraseOptions};
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

  /// Parser dialect. `auto` matches the default behaviour (try TS then TSX).
  #[arg(
    long,
    value_enum,
    default_value_t = DialectArg::Auto,
    value_name = "auto|js|jsx|ts|tsx|dts"
  )]
  dialect: DialectArg,

  /// Lower TypeScript class fields to constructor assignments/`Object.defineProperty`.
  #[arg(long)]
  ts_lower_class_fields: bool,

  /// TypeScript class field semantics when lowering (`true` uses `Object.defineProperty`).
  #[arg(
    long,
    action = ArgAction::Set,
    default_value_t = true,
    value_name = "true|false"
  )]
  ts_use_define_for_class_fields: bool,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum DialectArg {
  Auto,
  Js,
  Jsx,
  Ts,
  Tsx,
  Dts,
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

fn exit_with_host_error(name: &str, text: &str, message: impl Into<String>) -> ! {
  let diagnostic = host_error(
    Some(Span::new(FileId(0), TextRange::new(0, 0))),
    message.into(),
  );
  let provider = SingleFileSource {
    name: name.to_string(),
    text,
  };
  eprintln!("{}", render_diagnostic(&provider, &diagnostic));
  process::exit(1);
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
        exit_with_host_error(
          &input_name,
          "",
          format!("failed to open {}: {err}", p.display()),
        );
      }
    },
    None => Box::new(stdin()),
  };
  if let Err(err) = input_file.read_to_end(&mut input) {
    exit_with_host_error(&input_name, "", format!("failed to read input: {err}"));
  }
  let source = match std::str::from_utf8(&input) {
    Ok(source) => source,
    Err(err) => {
      exit_with_host_error(&input_name, "", format!("input is not valid UTF-8: {err}"));
    }
  };
  let mut output = Vec::new();
  let ts_erase_options = TsEraseOptions {
    lower_class_fields: args.ts_lower_class_fields,
    use_define_for_class_fields: args.ts_use_define_for_class_fields,
    ..TsEraseOptions::default()
  };
  let mut options = MinifyOptions::new(args.mode).with_ts_erase_options(ts_erase_options);
  if let Some(dialect) = match args.dialect {
    DialectArg::Auto => None,
    DialectArg::Js => Some(Dialect::Js),
    DialectArg::Jsx => Some(Dialect::Jsx),
    DialectArg::Ts => Some(Dialect::Ts),
    DialectArg::Tsx => Some(Dialect::Tsx),
    DialectArg::Dts => Some(Dialect::Dts),
  } {
    options = options.with_dialect(dialect);
  }
  match minify_with_options(options, source, &mut output) {
    Ok(()) => {
      let write_result = match args.output.as_ref() {
        Some(p) => File::create(p)
          .and_then(|mut file| file.write_all(&output))
          .map_err(|err| (p.display().to_string(), err)),
        None => stdout()
          .write_all(&output)
          .map_err(|err| ("<stdout>".to_string(), err)),
      };
      if let Err((dest, err)) = write_result {
        exit_with_host_error(&dest, source, format!("failed to write output: {err}"));
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
