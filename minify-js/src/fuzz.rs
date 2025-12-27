use diagnostics::FileId;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

use crate::ts_erase::erase_types;
use crate::{minify_with_options, MinifyOptions, TopLevelMode};

/// Fuzz entry point that parses, erases TypeScript syntax, and runs the full
/// minifier without panicking.
#[doc(hidden)]
pub fn fuzz_minify_pipeline(data: &[u8]) {
  let source = String::from_utf8_lossy(data).into_owned();
  let file = FileId(0);

  // Attempt to parse as TypeScript first, then TSX to exercise erasure on both
  // dialects before falling back to the full minify pipeline.
  let mut last_error = None;
  for dialect in [Dialect::Ts, Dialect::Tsx] {
    let parse_opts = ParseOptions {
      dialect,
      source_type: SourceType::Module,
    };
    match parse_with_options(&source, parse_opts) {
      Ok(mut ast) => {
        let _ = erase_types(file, &mut ast);
        break;
      }
      Err(err) => last_error = Some(err),
    }
  }
  if let Some(err) = last_error {
    let _ = err.to_diagnostic(file);
  }

  let mut output = Vec::new();
  let _ = minify_with_options(
    MinifyOptions::new(TopLevelMode::Module),
    &source,
    &mut output,
  );
}
