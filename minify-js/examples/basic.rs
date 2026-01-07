use diagnostics::render::render_diagnostic;
use diagnostics::{sort_diagnostics, SimpleFiles};
use minify_js::{minify, TopLevelMode};

const SOURCE: &str = r#"export const answer: number = 42;
export function add(a: number, b: number) {
  return a + b;
}
"#;

fn main() {
  let mut out = Vec::new();
  match minify(TopLevelMode::Module, SOURCE, &mut out) {
    Ok(()) => {
      let code = String::from_utf8(out).expect("minify-js emits UTF-8");
      println!("{code}");
    }
    Err(mut diagnostics) => {
      sort_diagnostics(&mut diagnostics);
      let mut files = SimpleFiles::new();
      let _file = files.add("example.ts", SOURCE);
      for diagnostic in &diagnostics {
        print!("{}", render_diagnostic(&files, diagnostic));
      }
    }
  }
}

