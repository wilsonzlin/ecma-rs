//! Bind the test262 parser `pass/` corpus with JS-mode `bind_js`.
//!
//! The test262 harness currently binds only `early/` (the harness/manifest are
//! owned elsewhere). This integration test proves the binder no longer rejects
//! legal sloppy scripts from the pass corpus — without touching the frozen
//! harness. Extending the harness to bind `pass/` is a one-line follow-up.
//!
//! Skips cleanly when the submodule directory is absent (CI without submodules).

use diagnostics::{FileId, Severity};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::js::{bind_js, TopLevelMode};
use std::fs;
use std::path::PathBuf;

#[test]
fn test262_pass_corpus_has_zero_bind_false_positives() {
  let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../test262/data/pass");
  if !dir.is_dir() {
    eprintln!("skip: test262/data/pass not present (submodule not checked out)");
    return;
  }

  let mut entries: Vec<_> = fs::read_dir(&dir)
    .expect("read pass dir")
    .map(|e| e.expect("dir entry"))
    .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("js"))
    .collect();
  entries.sort_by_key(|e| e.file_name());

  let mut false_positives: Vec<(String, Vec<String>)> = Vec::new();
  let mut parse_failures: Vec<String> = Vec::new();

  for ent in entries {
    let path = ent.path();
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let source = fs::read_to_string(&path).expect("read source");
    // Harness convention: `.module.` in the filename ⇒ module source type.
    let is_module = name.contains(".module.");
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: if is_module {
        SourceType::Module
      } else {
        SourceType::Script
      },
    };
    let mut ast = match parse_with_options(&source, opts) {
      Ok(ast) => ast,
      Err(_) => {
        // Parser-owned failures are out of scope for this binder check.
        parse_failures.push(name);
        continue;
      }
    };
    let mode = if is_module {
      TopLevelMode::Module
    } else {
      TopLevelMode::Script
    };
    let (_sem, diagnostics) = bind_js(&mut ast, mode, FileId(0));
    let binds: Vec<String> = diagnostics
      .into_iter()
      .filter(|d| d.severity == Severity::Error)
      .filter(|d| d.code.as_str().starts_with("BIND"))
      // TDZ is a runtime ReferenceError, not an early error (harness excludes it too).
      .filter(|d| d.code.as_str() != "BIND0003")
      .map(|d| d.code.as_str().to_string())
      .collect();
    if !binds.is_empty() {
      false_positives.push((name, binds));
    }
  }

  if !false_positives.is_empty() {
    let mut msg = format!(
      "expected 0 BIND false positives on test262 pass corpus, found {}\n",
      false_positives.len()
    );
    for (name, codes) in &false_positives {
      msg.push_str(&format!("  {name}: {}\n", codes.join(", ")));
    }
    panic!("{msg}");
  }

  eprintln!(
    "pass-corpus bind: 0 BIND false positives ({} parse failures skipped)",
    parse_failures.len()
  );
}
