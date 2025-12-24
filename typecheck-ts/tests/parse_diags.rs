use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{diagnostic_from_syntax_error, FileId, TextRange};
use typecheck_ts::queries::parse;

struct SingleFile<'a> {
  name: &'a str,
  text: &'a str,
}

impl<'a> SourceProvider for SingleFile<'a> {
  fn file_name(&self, _file: FileId) -> &str {
    self.name
  }

  fn file_text(&self, _file: FileId) -> &str {
    self.text
  }
}

#[test]
fn reports_diagnostic_with_span_for_invalid_syntax() {
  let file = FileId(0);
  let source = "function missingBrace(";

  let result = parse::parse(file, source);

  assert!(result.ast.is_none());
  assert_eq!(result.diagnostics.len(), 1);

  let diagnostic = &result.diagnostics[0];
  let syntax_error = parse_js::parse(source).unwrap_err();
  let expected = diagnostic_from_syntax_error(file, &syntax_error);

  assert_eq!(*diagnostic, expected);
  assert_eq!(diagnostic.primary.file, file);
  assert_eq!(diagnostic.primary.range, TextRange::from(syntax_error.loc));

  let rendered = render_diagnostic(
    &SingleFile {
      name: "test.ts",
      text: source,
    },
    diagnostic,
  );
  let expected_position = format!("--> test.ts:1:{}", diagnostic.primary.range.start + 1);

  assert!(
    rendered.contains(&expected_position),
    "rendered diagnostic should include file/line/column, got:\n{rendered}"
  );
}
