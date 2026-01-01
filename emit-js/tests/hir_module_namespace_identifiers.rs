use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use serde_json::Value;

mod util;

fn syntax_value(source: &str) -> Value {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let ast = parse_with_options(source, opts).expect("parse source");
  util::serialize_without_locs(&ast)
}

fn roundtrip(source: &str, expected: &str) {
  let lowered = lower_from_source_with_kind(FileKind::Ts, source)
    .unwrap_or_else(|err| panic!("lower: {err:?}"));
  let emitted =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit lowered program");
  assert_eq!(emitted, expected);

  let original = syntax_value(source);
  let reparsed = syntax_value(&emitted);
  assert_eq!(
    original, reparsed,
    "roundtrip via HIR changed syntax\nsource: {source}\nemitted: {emitted}"
  );

  let emitted2 =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit second pass");
  assert_eq!(emitted2, emitted, "HIR emission must be deterministic");
}

#[test]
fn hir_emits_string_literal_export_alias() {
  roundtrip("export { a as \"a-b\" };", "export{a as\"a-b\"};");
}

#[test]
fn hir_emits_string_literal_export_star_alias() {
  roundtrip(
    "export * as \"ns-name\" from \"mod\";",
    "export*as\"ns-name\"from\"mod\";",
  );
}

#[test]
fn hir_emits_string_literal_import_alias() {
  roundtrip(
    "import { \"a-b\" as \"c-d\" } from \"x\";",
    "import{\"a-b\"as\"c-d\"}from\"x\";",
  );
}

#[test]
fn hir_keeps_as_for_string_import_when_alias_matches() {
  roundtrip(
    "import { \"a-b\" as \"a-b\" } from \"x\";",
    "import{\"a-b\"as\"a-b\"}from\"x\";",
  );
}

#[test]
fn hir_keeps_as_for_string_export_when_alias_matches() {
  roundtrip(
    "export { \"a-b\" as \"a-b\" } from \"x\";",
    "export{\"a-b\"as\"a-b\"}from\"x\";",
  );
}
