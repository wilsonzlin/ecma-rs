//! Parse → emit → parse → emit fixpoint over the `megatest/*.js` corpus.
//!
//! For each file that parses, both minified and canonical AST emission must
//! re-parse and re-emit to an identical string (emit-text fixpoint). The HIR
//! backend is checked the same way where emission is supported.
//!
//! Intentional non-participants are listed below with reasons — expand the
//! corpus coverage by deleting skip entries as gaps close, never by weakening
//! the fixpoint assertion.

use std::fs;
use std::path::{Path, PathBuf};

use diagnostics::FileId;
use emit_js::{emit_hir_file_to_string, emit_top_level_diagnostic, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

/// Files that currently fail to parse (documented corpus outliers).
const PARSE_SKIP: &[(&str, &str)] = &[
  (
    "vdom.js",
    "object literal `get:`/`set:` properties fail to parse (getter/setter ambiguity)",
  ),
  (
    "weird.js",
    "object literal `get:`/`set:` properties fail to parse (getter/setter ambiguity)",
  ),
];

/// Files that parse and AST-fixpoint, but HIR emit hits `ExprKind::Missing`.
const HIR_EMIT_SKIP: &[(&str, &str)] = &[
  (
    "reactive_pipeline.js",
    "HIR lowering leaves ExprKind::Missing; emit fails closed",
  ),
  (
    "static_analysis.js",
    "HIR lowering leaves ExprKind::Missing; emit fails closed",
  ),
  (
    "stream_processing.js",
    "HIR lowering leaves ExprKind::Missing; emit fails closed",
  ),
  (
    "task_scheduler.js",
    "HIR lowering leaves ExprKind::Missing; emit fails closed",
  ),
];

fn megatest_dir() -> PathBuf {
  PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../megatest")
}

fn megatest_js_files() -> Vec<PathBuf> {
  let dir = megatest_dir();
  let mut files: Vec<_> = fs::read_dir(&dir)
    .unwrap_or_else(|err| panic!("read megatest dir {}: {err}", dir.display()))
    .filter_map(|entry| entry.ok())
    .map(|entry| entry.path())
    .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("js"))
    .collect();
  files.sort();
  assert!(
    !files.is_empty(),
    "expected megatest/*.js under {}",
    dir.display()
  );
  files
}

fn file_name(path: &Path) -> &str {
  path
    .file_name()
    .and_then(|name| name.to_str())
    .expect("utf-8 filename")
}

fn skip_reason<'a>(table: &'a [(&str, &str)], name: &str) -> Option<&'a str> {
  table
    .iter()
    .find_map(|(file, reason)| (*file == name).then_some(*reason))
}

fn parse_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

fn assert_ast_emit_fixpoint(name: &str, source: &str, emit_opts: EmitOptions, mode: &str) {
  let opts = parse_opts();
  let first = parse_with_options(source, opts)
    .unwrap_or_else(|err| panic!("{name}: initial parse failed: {err:?}"));
  let emitted1 = emit_top_level_diagnostic(FileId(0), &first, emit_opts).unwrap_or_else(|err| {
    panic!("{name}: AST {mode} emit failed: {err:?}");
  });
  let second = parse_with_options(&emitted1, opts).unwrap_or_else(|err| {
    panic!(
      "{name}: AST {mode} emitted text failed to re-parse ({err:?})\n--- emitted ---\n{emitted1}"
    );
  });
  let emitted2 = emit_top_level_diagnostic(FileId(0), &second, emit_opts).unwrap_or_else(|err| {
    panic!("{name}: AST {mode} re-emit failed: {err:?}");
  });
  assert_eq!(
    emitted1, emitted2,
    "{name}: AST {mode} emit text is not a fixpoint\n--- emit1 ---\n{emitted1}\n--- emit2 ---\n{emitted2}"
  );
}

fn assert_hir_emit_fixpoint(name: &str, source: &str, emit_opts: EmitOptions, mode: &str) {
  let first = lower_from_source_with_kind(FileKind::Js, source)
    .unwrap_or_else(|err| panic!("{name}: HIR lower failed: {err:?}"));
  let emitted1 = emit_hir_file_to_string(&first, emit_opts).unwrap_or_else(|err| {
    panic!("{name}: HIR {mode} emit failed: {err:?}");
  });
  // Re-parse through the source path so we exercise parse→lower→emit, not just
  // lower→emit identity on the same LowerResult.
  let second = lower_from_source_with_kind(FileKind::Js, &emitted1).unwrap_or_else(|err| {
    panic!(
      "{name}: HIR {mode} emitted text failed to re-lower ({err:?})\n--- emitted ---\n{emitted1}"
    );
  });
  let emitted2 = emit_hir_file_to_string(&second, emit_opts).unwrap_or_else(|err| {
    panic!("{name}: HIR {mode} re-emit failed: {err:?}");
  });
  assert_eq!(
    emitted1, emitted2,
    "{name}: HIR {mode} emit text is not a fixpoint\n--- emit1 ---\n{emitted1}\n--- emit2 ---\n{emitted2}"
  );
}

#[test]
fn megatest_ast_emit_text_is_fixpoint() {
  let mut checked = 0usize;
  for path in megatest_js_files() {
    let name = file_name(&path).to_string();
    if let Some(reason) = skip_reason(PARSE_SKIP, &name) {
      eprintln!("SKIP parse {name}: {reason}");
      continue;
    }
    let source =
      fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
    assert_ast_emit_fixpoint(&name, &source, EmitOptions::minified(), "minified");
    assert_ast_emit_fixpoint(&name, &source, EmitOptions::canonical(), "canonical");
    checked += 1;
  }
  assert!(
    checked >= 11,
    "expected at least 11 megatest files under AST fixpoint, got {checked}"
  );
}

#[test]
fn megatest_hir_emit_text_is_fixpoint_where_supported() {
  let mut checked = 0usize;
  for path in megatest_js_files() {
    let name = file_name(&path).to_string();
    if let Some(reason) = skip_reason(PARSE_SKIP, &name) {
      eprintln!("SKIP parse {name}: {reason}");
      continue;
    }
    if let Some(reason) = skip_reason(HIR_EMIT_SKIP, &name) {
      eprintln!("SKIP hir-emit {name}: {reason}");
      continue;
    }
    let source =
      fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
    assert_hir_emit_fixpoint(&name, &source, EmitOptions::minified(), "minified");
    assert_hir_emit_fixpoint(&name, &source, EmitOptions::canonical(), "canonical");
    checked += 1;
  }
  assert!(
    checked >= 7,
    "expected at least 7 megatest files under HIR fixpoint, got {checked}"
  );
}

#[test]
fn megatest_skip_tables_name_existing_files() {
  let names: Vec<_> = megatest_js_files()
    .into_iter()
    .map(|path| file_name(&path).to_string())
    .collect();
  for (file, _) in PARSE_SKIP.iter().chain(HIR_EMIT_SKIP.iter()) {
    assert!(
      names.iter().any(|name| name == *file),
      "skip entry `{file}` is not a megatest/*.js file (stale skip?)"
    );
  }
}
