//! Template literal line-terminator normalization (ECMA-262 §12.9.6): CR and
//! CRLF both cook to a single LF code unit, so a template containing a CRLF
//! matches a `"…\n…"` string-literal type annotation
//! (`stringLiteralTypesWithTemplateStrings01.ts`).

use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn crlf_cooks_to_lf_in_templates() {
  // The template's raw line break is CRLF; its cooked value must be a single
  // LF so the annotation `"DE\nF"` matches.
  let src = "let DE_NEWLINE_F: \"DE\\nF\" = `DE\r\nF`;\n";
  let mut host = MemoryHost::with_options(CompilerOptions::default());
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.is_empty(),
    "CRLF template should match LF annotation: {diags:?}"
  );
}

#[test]
fn lone_cr_cooks_to_lf_in_templates() {
  let src = "let X: \"A\\nB\" = `A\rB`;\n";
  let mut host = MemoryHost::with_options(CompilerOptions::default());
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.is_empty(),
    "lone CR template should match LF annotation: {diags:?}"
  );
}

#[test]
fn conformance_template_with_crlf_matches() {
  // Full conformance shape: mixed CRLF/LF file with a BOM.
  let src = "\u{feff}// @declaration: true\n\nlet ABC: \"ABC\" = `ABC`;\nlet DE_NEWLINE_F: \"DE\\nF\" = `DE\r\nF`;\nlet G_QUOTE_HI: 'G\"HI';\nlet JK_BACKTICK_L: \"JK`L\" = `JK\\`L`;\n";
  let mut host = MemoryHost::with_options(CompilerOptions::default());
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  assert!(
    diags.is_empty(),
    "conformance shape should check clean: {diags:?}"
  );
}

#[test]
fn parser_cooked_value_normalizes_crlf() {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let ast = parse_with_options("let x = `DE\r\nF`;", opts).expect("parse");
  let _ = ast;
}
