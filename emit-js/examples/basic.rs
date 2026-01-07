use diagnostics::render::render_diagnostic;
use diagnostics::SimpleFiles;
use diagnostics::{Diagnostic, FileId};
use emit_js::{emit_top_level_diagnostic, EmitOptions};
use parse_js::parse;

const SOURCE: &str = r#"export interface Point {
  x: number;
  y: number;
}

export function add(a: number, b: number) {
  return a + b;
}
"#;

fn main() {
  let file = FileId(0);
  let ast = parse(SOURCE).expect("parse succeeds");

  match emit_top_level_diagnostic(file, &ast, EmitOptions::minified()) {
    Ok(minified) => {
      println!("{minified}");
    }
    Err(diagnostic) => {
      render_and_print(file, diagnostic);
    }
  }
}

fn render_and_print(file: FileId, diagnostic: Diagnostic) {
  let mut files = SimpleFiles::new();
  files.add("example.ts", SOURCE);
  // The diagnostic references `FileId(0)` which matches the inserted file.
  debug_assert_eq!(file, FileId(0));
  print!("{}", render_diagnostic(&files, &diagnostic));
}

