use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{FileId, TextRange};
use std::sync::Arc;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::queries::parse;
use typecheck_ts::{codes, FileKey, Host, HostError, Program};

struct SingleFile<'a> {
  name: &'a str,
  text: &'a str,
}

impl<'a> SourceProvider for SingleFile<'a> {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some(self.name)
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    Some(self.text)
  }
}

#[test]
fn reports_diagnostic_with_span_for_invalid_syntax() {
  let file = FileId(0);
  let source = "function missingBrace(";

  let result = parse::parse(file, FileKind::Ts, source);

  assert!(result.ast.is_none());
  assert_eq!(result.diagnostics.len(), 1);

  let diagnostic = &result.diagnostics[0];
  let syntax_error = parse_js::parse(source).unwrap_err();
  let expected = syntax_error.to_diagnostic(file);

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

struct MissingImportHost {
  text: Arc<str>,
}

impl Host for MissingImportHost {
  fn file_text(&self, _file: &FileKey) -> Result<Arc<str>, HostError> {
    Ok(self.text.clone())
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }
}

#[test]
fn unresolved_import_points_at_specifier() {
  let source = r#"import { Foo } from "./missing";"#;
  let host = MissingImportHost {
    text: Arc::from(source.to_string()),
  };

  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let diagnostics = program.check();
  let file_id = program.file_id(&FileKey::new("entry.ts")).unwrap();
  assert_eq!(diagnostics.len(), 1);

  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::UNRESOLVED_MODULE.as_str());
  assert_eq!(diag.primary.file, file_id);

  let specifier = "\"./missing\"";
  let start = source.find(specifier).expect("missing specifier in source") as u32;
  let end = start + specifier.len() as u32;
  let expected_span = TextRange::new(start, end);
  assert!(
    diag.primary.range.start <= expected_span.start && diag.primary.range.end >= expected_span.end,
    "diagnostic span {:?} should cover specifier {:?}",
    diag.primary.range,
    expected_span
  );
}
