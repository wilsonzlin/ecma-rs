use diagnostics::files::SimpleFiles;
use diagnostics::render::render_diagnostic;
use diagnostics::{Diagnostic, Label, Span, TextRange};
use std::path::PathBuf;

fn assert_snapshot(name: &str, actual: &str) {
  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
  let path = root.join("tests").join("snapshots").join(format!("{name}.snap"));
  let expected = std::fs::read_to_string(&path).expect("read snapshot");
  assert_eq!(actual, expected, "snapshot mismatch for {name}");
}

#[test]
fn snapshot_multi_file_diagnostic() {
  let mut files = SimpleFiles::new();
  let a = files.add("a.js", "const a = 1;\n");
  let b = files.add("b.js", "const b = 2;\n");

  let diagnostic = Diagnostic::error(
    "TEST_MULTI_FILE",
    "uses two files",
    Span::new(b, TextRange::new(6, 7)),
  )
  .with_label(Label::secondary(
    Span::new(a, TextRange::new(6, 7)),
    "related symbol",
  ));

  let rendered = render_diagnostic(&files, &diagnostic);
  assert_snapshot("multi_file", &rendered);
}

#[test]
fn snapshot_multi_line_label() {
  let mut files = SimpleFiles::new();
  let text = "function test() {\n  return 1;\n}\n";
  let file = files.add("main.ts", text);

  let diagnostic = Diagnostic::error(
    "TEST_MULTI_LINE",
    "broken function",
    Span::new(file, TextRange::new(0, text.len() as u32)),
  );

  let rendered = render_diagnostic(&files, &diagnostic);
  assert_snapshot("multi_line_label", &rendered);
}

#[test]
fn snapshot_overlapping_label_ordering_is_stable() {
  let mut files = SimpleFiles::new();
  let file = files.add("order.js", "abcdefghij\n");

  let primary = Span::new(file, TextRange::new(2, 6));
  let overlap = Label::secondary(Span::new(file, TextRange::new(3, 5)), "overlap");
  let tail = Label::secondary(Span::new(file, TextRange::new(7, 10)), "tail");

  let diagnostic_a = Diagnostic::error("TEST_OVERLAP", "main", primary)
    .with_label(tail.clone())
    .with_label(overlap.clone());
  let diagnostic_b = Diagnostic::error("TEST_OVERLAP", "main", primary)
    .with_label(overlap)
    .with_label(tail);

  let rendered_a = render_diagnostic(&files, &diagnostic_a);
  let rendered_b = render_diagnostic(&files, &diagnostic_b);

  assert_eq!(
    rendered_a, rendered_b,
    "rendering must be deterministic regardless of label insertion order"
  );
  assert_snapshot("overlapping_labels", &rendered_a);
}

#[test]
fn snapshot_utf8_boundary_clamping() {
  let mut files = SimpleFiles::new();
  let file = files.add("utf8.js", "écho\n");

  let diagnostic = Diagnostic::error(
    "TEST_UTF8",
    "inside utf8 char",
    Span::new(file, TextRange::new(1, 2)),
  );

  let rendered = render_diagnostic(&files, &diagnostic);
  assert_snapshot("utf8_boundary", &rendered);
}
