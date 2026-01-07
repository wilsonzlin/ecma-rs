use diagnostics::render::render_diagnostic;
use diagnostics::{Diagnostic, Label, SimpleFiles, Span, TextRange};

fn main() {
  let mut files = SimpleFiles::new();
  let file = files.add("example.ts", "const answer: number = 42;\n");

  let diagnostic = Diagnostic::error(
    "TEST0001",
    "example diagnostic",
    Span {
      file,
      range: TextRange::new(6, 12), // highlights `answer`
    },
  )
  .with_label(Label::secondary(
    Span {
      file,
      range: TextRange::new(14, 20), // highlights `number`
    },
    "type annotation",
  ));

  print!("{}", render_diagnostic(&files, &diagnostic));
}

