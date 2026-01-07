use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

const SOURCE: &str = r#"export type Point = { x: number, y: number };
export const origin: Point = { x: 0, y: 0 };
"#;

fn main() {
  let parsed = parse_with_options(
    SOURCE,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  );

  match parsed {
    Ok(ast) => {
      println!("statements: {}", ast.stx.body.len());
      if let Some(first) = ast.stx.body.first() {
        println!("first_stmt_span: {}..{}", first.loc.0, first.loc.1);
      }
    }
    Err(err) => render_error(err),
  }
}

#[cfg(feature = "diagnostics")]
fn render_error(err: parse_js::error::SyntaxError) {
  use diagnostics::render::render_diagnostic;
  use diagnostics::SimpleFiles;
  use diagnostics::FileId;

  let mut files = SimpleFiles::new();
  let file = files.add("example.ts", SOURCE);
  let diagnostic = err.to_diagnostic(file);
  print!("{}", render_diagnostic(&files, &diagnostic));
}

#[cfg(not(feature = "diagnostics"))]
fn render_error(err: parse_js::error::SyntaxError) {
  eprintln!("parse error: {err}");
  eprintln!("span: {}..{}", err.loc.0, err.loc.1);
}

