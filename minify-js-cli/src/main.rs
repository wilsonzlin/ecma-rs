use clap::builder::PossibleValuesParser;
use clap::builder::TypedValueParser;
use clap::{ArgAction, Parser, ValueEnum};
use diagnostics::render::{render_diagnostic_with_options, RenderOptions, SourceProvider};
use diagnostics::{host_error, Diagnostic, FileId, Severity, Span, TextRange};
use minify_js::{
  minify_with_options, ConstEnumMode, Dialect, MinifyOptions, TopLevelMode, TsEraseOptions,
};
use serde::Serialize;
use std::fs::File;
use std::io::stdin;
use std::io::stdout;
use std::io::IsTerminal;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;
use std::process;

const JSON_SCHEMA_VERSION: u32 = 1;

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

  /// Emit versioned JSON output to stdout (schema_version = 1).
  #[arg(long)]
  json: bool,

  /// Force-enable ANSI colors in diagnostics output.
  #[arg(long)]
  color: bool,

  /// Disable ANSI colors in diagnostics output.
  #[arg(long)]
  no_color: bool,

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

  /// Preserve `const enum` declarations at runtime instead of inlining/erasing them.
  #[arg(long = "preserve-const-enums", alias = "ts-preserve-const-enums")]
  ts_preserve_const_enums: bool,
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

#[derive(Serialize)]
struct JsonOutput {
  schema_version: u32,
  mode: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  output: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  diagnostics: Option<Vec<Diagnostic>>,
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

fn mode_str(mode: TopLevelMode) -> &'static str {
  match mode {
    TopLevelMode::Global => "global",
    TopLevelMode::Module => "module",
  }
}

fn sort_diagnostics(diagnostics: &mut [Diagnostic]) {
  for diagnostic in diagnostics.iter_mut() {
    diagnostic.labels.sort();
  }
  diagnostics.sort_by(|a, b| {
    a.primary
      .file
      .cmp(&b.primary.file)
      .then(a.primary.range.start.cmp(&b.primary.range.start))
      .then(a.code.cmp(&b.code))
      .then(a.message.cmp(&b.message))
  });
}

fn write_json(output: &JsonOutput) -> Result<(), serde_json::Error> {
  let stdout = std::io::stdout();
  let mut handle = stdout.lock();
  serde_json::to_writer(&mut handle, output)?;
  writeln!(&mut handle).map_err(serde_json::Error::io)?;
  Ok(())
}

fn exit_with_diagnostics(
  mode: TopLevelMode,
  json: bool,
  provider: &dyn SourceProvider,
  mut diagnostics: Vec<Diagnostic>,
  render_options: RenderOptions,
) -> ! {
  sort_diagnostics(&mut diagnostics);
  let exit_code = if diagnostics
    .iter()
    .any(|diagnostic| diagnostic.severity == Severity::Error)
  {
    1
  } else {
    0
  };

  if json {
    let output = JsonOutput {
      schema_version: JSON_SCHEMA_VERSION,
      mode: mode_str(mode).to_string(),
      output: None,
      diagnostics: Some(diagnostics),
    };
    if let Err(err) = write_json(&output) {
      eprintln!("failed to serialize JSON: {err}");
      process::exit(1);
    }
  } else {
    for diagnostic in diagnostics {
      eprintln!(
        "{}",
        render_diagnostic_with_options(provider, &diagnostic, render_options)
      );
    }
  }

  process::exit(exit_code);
}

fn exit_with_host_error(
  input_name: &str,
  mode: TopLevelMode,
  json: bool,
  text: &str,
  message: impl Into<String>,
  render_options: RenderOptions,
) -> ! {
  let diagnostic = host_error(
    Some(Span::new(FileId(0), TextRange::new(0, 0))),
    message.into(),
  );
  let provider = SingleFileSource {
    name: input_name.to_string(),
    text,
  };
  exit_with_diagnostics(mode, json, &provider, vec![diagnostic], render_options);
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
  let render_options = RenderOptions {
    context_lines: 1,
    color,
    ..RenderOptions::default()
  };
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
          args.mode,
          args.json,
          "",
          format!("failed to open {}: {err}", p.display()),
          render_options,
        );
      }
    },
    None => Box::new(stdin()),
  };
  if let Err(err) = input_file.read_to_end(&mut input) {
    exit_with_host_error(
      &input_name,
      args.mode,
      args.json,
      "",
      format!("failed to read input: {err}"),
      render_options,
    );
  }
  let source = match std::str::from_utf8(&input) {
    Ok(source) => source,
    Err(err) => {
      exit_with_host_error(
        &input_name,
        args.mode,
        args.json,
        "",
        format!("input is not valid UTF-8: {err}"),
        render_options,
      );
    }
  };
  let mut output = Vec::new();
  let ts_erase_options = TsEraseOptions {
    lower_class_fields: args.ts_lower_class_fields,
    use_define_for_class_fields: args.ts_use_define_for_class_fields,
    const_enum_mode: if args.ts_preserve_const_enums {
      ConstEnumMode::Runtime
    } else {
      ConstEnumMode::Inline
    },
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
      if let Some(p) = args.output.as_ref() {
        if let Err(err) = File::create(p).and_then(|mut file| file.write_all(&output)) {
          exit_with_host_error(
            &p.display().to_string(),
            args.mode,
            args.json,
            source,
            format!("failed to write output: {err}"),
            render_options,
          );
        }
      } else if !args.json {
        if let Err(err) = stdout().write_all(&output) {
          exit_with_host_error(
            "<stdout>",
            args.mode,
            false,
            source,
            format!("failed to write output: {err}"),
            render_options,
          );
        }
      }

      if args.json {
        let output_str = match String::from_utf8(output) {
          Ok(output_str) => output_str,
          Err(err) => {
            exit_with_host_error(
              &input_name,
              args.mode,
              true,
              source,
              format!("failed to serialize minified output as UTF-8: {err}"),
              render_options,
            );
          }
        };
        let output = JsonOutput {
          schema_version: JSON_SCHEMA_VERSION,
          mode: mode_str(args.mode).to_string(),
          output: Some(output_str),
          diagnostics: None,
        };
        if let Err(err) = write_json(&output) {
          eprintln!("failed to serialize JSON: {err}");
          process::exit(1);
        }
      }
    }
    Err(diagnostics) => {
      let provider = SingleFileSource {
        name: input_name,
        text: source,
      };
      exit_with_diagnostics(args.mode, args.json, &provider, diagnostics, render_options);
    }
  }
}
