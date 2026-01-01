use emit_js::{emit_program, EmitOptions, Emitter};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

mod util;

fn roundtrip(src: &str, expected: &str) {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let parsed = parse_with_options(src, opts).unwrap_or_else(|err| panic!("parse {src:?}: {err:?}"));
  let mut emitter = Emitter::new(EmitOptions::minified());
  emit_program(&mut emitter, parsed.stx.as_ref())
    .unwrap_or_else(|err| panic!("emit {src:?}: {err:?}"));
  let emitted = String::from_utf8(emitter.into_bytes()).expect("utf-8");
  assert_eq!(emitted, expected);

  let reparsed =
    parse_with_options(&emitted, opts).unwrap_or_else(|err| panic!("reparse {emitted:?}: {err:?}"));
  assert_eq!(
    util::serialize_without_locs(&parsed),
    util::serialize_without_locs(&reparsed),
    "emitted source: {emitted}"
  );

  // Ensure the output is deterministic when re-emitting the re-parsed program.
  let mut emitter2 = Emitter::new(EmitOptions::minified());
  emit_program(&mut emitter2, reparsed.stx.as_ref()).expect("emit second pass");
  let emitted2 = String::from_utf8(emitter2.into_bytes()).expect("utf-8");
  assert_eq!(emitted2, emitted, "emission must be deterministic");
}

#[test]
fn export_alias_can_be_string_literal() {
  roundtrip("export { a as \"a-b\" };", "export{a as\"a-b\"};");
}

#[test]
fn export_star_alias_can_be_string_literal() {
  roundtrip(
    "export * as \"ns-name\" from \"mod\";",
    "export*as\"ns-name\"from\"mod\";",
  );
}

#[test]
fn import_alias_can_be_string_literal() {
  roundtrip(
    "import { \"a-b\" as \"c-d\" } from \"x\";",
    "import{\"a-b\"as\"c-d\"}from\"x\";",
  );
}

#[test]
fn import_string_name_can_have_identifier_alias() {
  roundtrip(
    "import { \"a-b\" as bar } from \"x\";",
    "import{\"a-b\"as bar}from\"x\";",
  );
}

#[test]
fn import_type_alias_can_be_string_literal() {
  roundtrip(
    "import type { \"a-b\" as \"c-d\" } from \"x\";",
    "import type{\"a-b\"as\"c-d\"}from\"x\";",
  );
}

#[test]
fn export_type_alias_can_be_string_literal() {
  roundtrip("export type { a as \"a-b\" };", "export type{a as\"a-b\"};");
}

#[test]
fn export_type_star_alias_can_be_string_literal() {
  roundtrip(
    "export type * as \"ns-name\" from \"mod\";",
    "export type*as\"ns-name\"from\"mod\";",
  );
}

#[test]
fn string_import_name_still_requires_as_when_alias_matches() {
  roundtrip(
    "import { \"a-b\" as \"a-b\" } from \"x\";",
    "import{\"a-b\"as\"a-b\"}from\"x\";",
  );
}

#[test]
fn string_export_name_still_requires_as_when_alias_matches() {
  roundtrip(
    "export { \"a-b\" as \"a-b\" } from \"x\";",
    "export{\"a-b\"as\"a-b\"}from\"x\";",
  );
}

#[test]
fn export_string_name_can_have_identifier_alias() {
  roundtrip(
    "export { \"a-b\" as bar } from \"x\";",
    "export{\"a-b\"as bar}from\"x\";",
  );
}

#[test]
fn reserved_keyword_alias_stays_quoted() {
  roundtrip("export { a as \"while\" };", "export{a as\"while\"};");
}

#[test]
fn keyword_import_name_still_requires_as_when_alias_matches() {
  roundtrip(
    "import { while as \"while\" } from \"x\";",
    "import{while as\"while\"}from\"x\";",
  );
}

#[test]
fn keyword_export_name_still_requires_as_when_alias_matches() {
  roundtrip(
    "export { while as \"while\" } from \"x\";",
    "export{while as\"while\"}from\"x\";",
  );
}

#[test]
fn export_star_reserved_keyword_alias_stays_quoted() {
  roundtrip(
    "export * as \"while\" from \"mod\";",
    "export*as\"while\"from\"mod\";",
  );
}

#[test]
fn escaped_identifier_alias_is_not_quoted() {
  roundtrip("export { a as \\u0061 };", "export{a as \\u0061};");
}
