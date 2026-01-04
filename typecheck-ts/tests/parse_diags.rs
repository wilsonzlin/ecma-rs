use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{Diagnostic, FileId, TextRange};
use parse_js::ast::stmt::Stmt;
use std::sync::Arc;
use std::thread;
use typecheck_ts::check::type_expr::TypeLowerer;
use typecheck_ts::db::{
  program_diagnostics as db_program_diagnostics, reset_parse_query_count,
  unresolved_module_diagnostics, TypecheckDb,
};
use typecheck_ts::lib_support::{CompilerOptions, FileKind, ModuleKind};
use typecheck_ts::queries::parse;
use typecheck_ts::{codes, FileKey, FileOrigin, Host, HostError, Program};
use types_ts_interned::TypeStore;

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
  options: CompilerOptions,
}

impl Host for MissingImportHost {
  fn file_text(&self, _file: &FileKey) -> Result<Arc<str>, HostError> {
    Ok(self.text.clone())
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

fn assert_unresolved_diag_covers_specifier(
  diag: &Diagnostic,
  file_id: FileId,
  source: &str,
  specifier: &str,
) {
  assert_eq!(diag.code.as_str(), codes::UNRESOLVED_MODULE.as_str());
  assert_eq!(diag.primary.file, file_id);

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

fn assert_diag_covers_substring(
  diag: &Diagnostic,
  expected_code: &codes::Code,
  file_id: FileId,
  source: &str,
  substring: &str,
) {
  assert_eq!(diag.code.as_str(), expected_code.as_str());
  assert_eq!(diag.primary.file, file_id);

  let start = source
    .find(substring)
    .unwrap_or_else(|| panic!("missing substring {substring:?} in source"));
  let start = start as u32;
  let end = start + substring.len() as u32;
  let expected_span = TextRange::new(start, end);
  assert!(
    diag.primary.range.start <= expected_span.start && diag.primary.range.end >= expected_span.end,
    "diagnostic span {:?} should cover substring {:?}",
    diag.primary.range,
    expected_span
  );
}

#[test]
fn unresolved_import_points_at_specifier() {
  let source = r#"import { Foo } from "./missing";"#;
  let host = MissingImportHost {
    text: Arc::from(source.to_string()),
    options: CompilerOptions::default(),
  };

  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let diagnostics = program.check();
  let file_id = program.file_id(&FileKey::new("entry.ts")).unwrap();
  assert_eq!(diagnostics.len(), 1);

  assert_unresolved_diag_covers_specifier(&diagnostics[0], file_id, source, "\"./missing\"");
}

#[test]
fn unresolved_import_type_points_at_specifier() {
  let source = r#"type T = import("./missing").Thing;"#;
  let host = MissingImportHost {
    text: Arc::from(source.to_string()),
    options: CompilerOptions::default(),
  };

  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let diagnostics = program.check();
  let file_id = program.file_id(&FileKey::new("entry.ts")).unwrap();

  let unresolved = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::UNRESOLVED_MODULE.as_str())
    .expect("expected UNRESOLVED_MODULE diagnostic");
  assert_unresolved_diag_covers_specifier(unresolved, file_id, source, "\"./missing\"");
}

#[test]
fn unresolved_typeof_import_points_at_specifier() {
  let source = r#"type T = typeof import("./missing").value;"#;
  let host = MissingImportHost {
    text: Arc::from(source.to_string()),
    options: CompilerOptions::default(),
  };

  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let diagnostics = program.check();
  let file_id = program.file_id(&FileKey::new("entry.ts")).unwrap();

  let unresolved = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::UNRESOLVED_MODULE.as_str())
    .expect("expected UNRESOLVED_MODULE diagnostic");
  assert_unresolved_diag_covers_specifier(unresolved, file_id, source, "\"./missing\"");
}

#[test]
fn unresolved_import_type_diagnostic_span_covers_expression() {
  let source = r#"type T = import("./dep");"#;
  let file = FileId(0);
  let parsed = parse::parse(file, FileKind::Ts, source);
  let ast = parsed.ast.expect("expected valid AST");
  let stmt = ast.stx.body.first().expect("expected statement");
  let Stmt::TypeAliasDecl(alias) = stmt.stx.as_ref() else {
    panic!("expected type alias declaration");
  };

  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store);
  lowerer.set_file(file);
  lowerer.lower_type_expr(&alias.stx.type_expr);
  let diagnostics = lowerer.take_diagnostics();

  let unresolved = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::UNRESOLVED_IMPORT_TYPE.as_str())
    .expect("expected UNRESOLVED_IMPORT_TYPE diagnostic from TypeLowerer");
  assert_diag_covers_substring(
    unresolved,
    &codes::UNRESOLVED_IMPORT_TYPE,
    file,
    source,
    "\"./dep\"",
  );
}

#[test]
fn unresolved_type_query_diagnostic_span_covers_reference() {
  let source = "type T = typeof missing;";
  let file = FileId(0);
  let parsed = parse::parse(file, FileKind::Ts, source);
  let ast = parsed.ast.expect("expected valid AST");
  let stmt = ast.stx.body.first().expect("expected statement");
  let Stmt::TypeAliasDecl(alias) = stmt.stx.as_ref() else {
    panic!("expected type alias declaration");
  };

  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store);
  lowerer.set_file(file);
  lowerer.lower_type_expr(&alias.stx.type_expr);
  let diagnostics = lowerer.take_diagnostics();

  let unresolved = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::UNRESOLVED_TYPE_QUERY.as_str())
    .expect("expected UNRESOLVED_TYPE_QUERY diagnostic from TypeLowerer");
  assert_diag_covers_substring(
    unresolved,
    &codes::UNRESOLVED_TYPE_QUERY,
    file,
    source,
    "missing",
  );
}

#[test]
fn unresolved_qualified_type_reference_span_covers_qualified_name() {
  let source = "type T = Foo.Bar;";
  let file = FileId(0);
  let parsed = parse::parse(file, FileKind::Ts, source);
  let ast = parsed.ast.expect("expected valid AST");
  let stmt = ast.stx.body.first().expect("expected statement");
  let Stmt::TypeAliasDecl(alias) = stmt.stx.as_ref() else {
    panic!("expected type alias declaration");
  };

  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store);
  lowerer.set_file(file);
  lowerer.lower_type_expr(&alias.stx.type_expr);
  let diagnostics = lowerer.take_diagnostics();

  let unresolved = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::UNSUPPORTED_QUALIFIED_NAME.as_str())
    .expect("expected UNSUPPORTED_QUALIFIED_NAME diagnostic from TypeLowerer");
  assert_diag_covers_substring(
    unresolved,
    &codes::UNSUPPORTED_QUALIFIED_NAME,
    file,
    source,
    "Foo.Bar",
  );
}

#[test]
fn unresolved_type_reference_span_covers_type_arguments() {
  let source = "type T = Foo<Bar>;";
  let file = FileId(0);
  let parsed = parse::parse(file, FileKind::Ts, source);
  let ast = parsed.ast.expect("expected valid AST");
  let stmt = ast.stx.body.first().expect("expected statement");
  let Stmt::TypeAliasDecl(alias) = stmt.stx.as_ref() else {
    panic!("expected type alias declaration");
  };

  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store);
  lowerer.set_file(file);
  lowerer.lower_type_expr(&alias.stx.type_expr);
  let diagnostics = lowerer.take_diagnostics();

  let unresolved = diagnostics
    .iter()
    .find(|diag| {
      diag.code.as_str() == codes::UNRESOLVED_TYPE_REFERENCE.as_str()
        && diag.message.contains("Foo")
    })
    .expect("expected UNRESOLVED_TYPE_REFERENCE diagnostic for Foo from TypeLowerer");
  assert_diag_covers_substring(
    unresolved,
    &codes::UNRESOLVED_TYPE_REFERENCE,
    file,
    source,
    "Foo<Bar>",
  );
}

#[test]
fn db_unresolved_import_points_at_specifier() {
  let source = r#"import { Foo } from "./missing";"#;
  let file = FileId(10);
  let key = FileKey::new("entry.ts");
  let mut db = TypecheckDb::default();
  db.set_roots(Arc::from([key.clone()]));
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from(source),
    FileOrigin::Source,
  );
  db.set_module_resolution(file, Arc::<str>::from("./missing"), None);

  let diags = unresolved_module_diagnostics(&db, file);
  assert_eq!(diags.len(), 1);
  assert_unresolved_diag_covers_specifier(&diags[0], file, source, "\"./missing\"");

  let program_diags = db_program_diagnostics(&db);
  assert_eq!(program_diags.len(), 1);
  assert_unresolved_diag_covers_specifier(&program_diags[0], file, source, "\"./missing\"");
}

#[test]
fn db_unresolved_import_type_points_at_specifier() {
  let source = r#"type T = import("./missing").Thing;"#;
  let file = FileId(12);
  let key = FileKey::new("entry.ts");
  let mut db = TypecheckDb::default();
  db.set_roots(Arc::from([key.clone()]));
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from(source),
    FileOrigin::Source,
  );
  db.set_module_resolution(file, Arc::<str>::from("./missing"), None);

  let diags = unresolved_module_diagnostics(&db, file);
  assert_eq!(diags.len(), 1);
  assert_unresolved_diag_covers_specifier(&diags[0], file, source, "\"./missing\"");
}

#[test]
fn db_unresolved_typeof_import_points_at_specifier() {
  let source = r#"type T = typeof import("./missing").value;"#;
  let file = FileId(13);
  let key = FileKey::new("entry.ts");
  let mut db = TypecheckDb::default();
  db.set_roots(Arc::from([key.clone()]));
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from(source),
    FileOrigin::Source,
  );
  db.set_module_resolution(file, Arc::<str>::from("./missing"), None);

  let diags = unresolved_module_diagnostics(&db, file);
  assert_eq!(diags.len(), 1);
  assert_unresolved_diag_covers_specifier(&diags[0], file, source, "\"./missing\"");
}

#[test]
fn db_unresolved_export_all_and_import_equals_point_at_specifier() {
  let source = r#"import foo = require("./missing-import-equals");
 export * from "./missing-export-all";"#;
  let file = FileId(11);
  let key = FileKey::new("entry.ts");
  let mut db = TypecheckDb::default();
  db.set_roots(Arc::from([key.clone()]));
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from(source),
    FileOrigin::Source,
  );
  db.set_module_resolution(file, Arc::<str>::from("./missing-import-equals"), None);
  db.set_module_resolution(file, Arc::<str>::from("./missing-export-all"), None);

  let mut diags: Vec<_> = unresolved_module_diagnostics(&db, file).as_ref().to_vec();
  assert_eq!(diags.len(), 2);
  diags.sort_by_key(|diag| diag.primary.range.start);

  assert_unresolved_diag_covers_specifier(&diags[0], file, source, "\"./missing-import-equals\"");
  assert_unresolved_diag_covers_specifier(&diags[1], file, source, "\"./missing-export-all\"");

  let mut program_diags: Vec<_> = db_program_diagnostics(&db).as_ref().to_vec();
  program_diags.sort_by_key(|diag| diag.primary.range.start);
  assert_eq!(program_diags.len(), 2);
  assert_unresolved_diag_covers_specifier(
    &program_diags[0],
    file,
    source,
    "\"./missing-import-equals\"",
  );
  assert_unresolved_diag_covers_specifier(
    &program_diags[1],
    file,
    source,
    "\"./missing-export-all\"",
  );
}

#[test]
fn program_unresolved_export_all_and_import_equals_point_at_specifier() {
  let source = r#"import foo = require("./missing-import-equals");
 export * from "./missing-export-all";"#;
  let mut options = CompilerOptions::default();
  options.module = Some(ModuleKind::CommonJs);
  let host = MissingImportHost {
    text: Arc::from(source.to_string()),
    options,
  };

  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let mut diagnostics = program.check();
  let file_id = program.file_id(&FileKey::new("entry.ts")).unwrap();
  diagnostics.sort_by_key(|diag| diag.primary.range.start);
  assert_eq!(diagnostics.len(), 2);

  assert_unresolved_diag_covers_specifier(
    &diagnostics[0],
    file_id,
    source,
    "\"./missing-import-equals\"",
  );
  assert_unresolved_diag_covers_specifier(
    &diagnostics[1],
    file_id,
    source,
    "\"./missing-export-all\"",
  );
}

#[test]
fn db_parse_reports_diagnostic_with_span_for_invalid_syntax() {
  let file = FileId(0);
  let key = FileKey::new("test.ts");
  let source = "function missingBrace(";
  let mut db = TypecheckDb::default();
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from(source),
    FileOrigin::Source,
  );

  let result = db.parse(file);

  assert!(result.ast.is_none());
  assert_eq!(result.diagnostics.len(), 1);
  let expected = parse_js::parse(source).unwrap_err().to_diagnostic(file);
  assert_eq!(result.diagnostics[0], expected);
}

#[test]
fn parse_query_is_memoized() {
  let file = FileId(0);
  let key = FileKey::new("memoized.ts");
  let mut db = TypecheckDb::default();
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from("const value = 1;"),
    FileOrigin::Source,
  );

  reset_parse_query_count();
  let first = db.parse(file);
  assert!(first.ast.is_some());

  let second = db.parse(file);
  assert_eq!(first, second);

  let lowered = db.lower_hir(file);
  assert!(lowered.lowered.is_some());
}

#[test]
fn concurrent_snapshots_share_results() {
  let file = FileId(0);
  let key = FileKey::new("add.ts");
  let mut db = TypecheckDb::default();
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from("export function add(a: number, b: number) { return a + b; }"),
    FileOrigin::Source,
  );

  let snapshot_a = db.snapshot();
  let snapshot_b = db.snapshot();

  let parsed = thread::spawn(move || snapshot_a.parse(file))
    .join()
    .expect("parse thread panicked");
  let lowered = thread::spawn(move || snapshot_b.lower_hir(file))
    .join()
    .expect("lower thread panicked");

  assert!(parsed.diagnostics.is_empty());
  assert!(lowered.diagnostics.is_empty());

  let parsed_again = db.parse(file);
  assert_eq!(
    parsed, parsed_again,
    "snapshots should populate the shared cache"
  );

  let lowered_again = db.lower_hir(file);
  assert_eq!(lowered.diagnostics, lowered_again.diagnostics);
  assert_eq!(lowered.lowered.as_ref(), lowered_again.lowered.as_ref());

  let sem_from_thread = db.snapshot().sem_hir(file);
  let sem_from_main = db.sem_hir(file);
  assert_eq!(sem_from_thread, sem_from_main);
}
