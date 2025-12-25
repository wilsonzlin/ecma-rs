use parse_js::error::SyntaxErrorType;
use parse_js::{parse, parse_with_options, Dialect, ParseOptions, SourceType};

#[test]
fn import_must_be_top_level_in_modules() {
  let err = parse("if (true) { import a from \"mod\"; }").unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("import declarations must be at top level")
  );
}

#[test]
fn export_must_be_top_level_in_modules() {
  let err = parse("function f() { export {}; }").unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("export declarations must be at top level")
  );
}

#[test]
fn scripts_do_not_allow_imports() {
  let err = parse_with_options(
    "import a from \"mod\";",
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Script,
    },
  )
  .unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("import not allowed in scripts")
  );
}
