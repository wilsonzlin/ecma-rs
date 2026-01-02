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
fn export_star_alias_can_be_default_keyword() {
  roundtrip(
    "export * as default from \"mod\";",
    "export*as default from\"mod\";",
  );
}

#[test]
fn import_star_alias_is_identifier() {
  roundtrip("import * as ns from \"mod\";", "import*as ns from\"mod\";");
}

#[test]
fn export_alias_can_be_default_keyword() {
  roundtrip("export { a as default };", "export{a as default};");
}

#[test]
fn reexport_default_name_does_not_require_as() {
  roundtrip(
    "export { default } from \"mod\";",
    "export{default}from\"mod\";",
  );
}

#[test]
fn reexport_default_can_be_aliased() {
  roundtrip(
    "export { default as foo } from \"mod\";",
    "export{default as foo}from\"mod\";",
  );
}

#[test]
fn reexport_default_can_be_aliased_to_string_literal() {
  roundtrip(
    r#"export { default as "a-b" } from "mod";"#,
    r#"export{default as"a-b"}from"mod";"#,
  );
}

#[test]
fn reexport_named_can_be_aliased_as_default() {
  roundtrip(
    "export { foo as default } from \"mod\";",
    "export{foo as default}from\"mod\";",
  );
}

#[test]
fn reexport_string_name_can_be_aliased_as_default() {
  roundtrip(
    r#"export { "a-b" as default } from "mod";"#,
    r#"export{"a-b"as default}from"mod";"#,
  );
}

#[test]
fn import_named_default_requires_as() {
  roundtrip(
    "import { default as foo } from \"mod\";",
    "import{default as foo}from\"mod\";",
  );
}

#[test]
fn import_type_named_default_requires_as() {
  roundtrip(
    r#"import type { default as foo } from "mod";"#,
    r#"import type{default as foo}from"mod";"#,
  );
}

#[test]
fn named_default_import_can_be_exported_as_default() {
  roundtrip(
    r#"import { default as foo } from "mod";export { foo as default };"#,
    r#"import{default as foo}from"mod";export{foo as default};"#,
  );
}

#[test]
fn string_import_name_can_be_exported_under_string_name() {
  roundtrip(
    "import { \"a-b\" as c } from \"x\"; export { c as \"e-f\" };",
    "import{\"a-b\"as c}from\"x\";export{c as\"e-f\"};",
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
    "import type { \"a-b\" as Foo } from \"x\";",
    "import type{\"a-b\"as Foo}from\"x\";",
  );
}

#[test]
fn import_type_star_alias_is_identifier() {
  roundtrip(
    "import type * as ns from \"mod\";",
    "import type*as ns from\"mod\";",
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
fn export_type_star_alias_can_be_default_keyword() {
  roundtrip(
    "export type * as default from \"mod\";",
    "export type*as default from\"mod\";",
  );
}

#[test]
fn export_type_default_can_be_aliased() {
  roundtrip(
    "export type { default as foo } from \"mod\";",
    "export type{default as foo}from\"mod\";",
  );
}

#[test]
fn export_type_default_can_be_aliased_to_string_literal() {
  roundtrip(
    r#"export type { default as "a-b" } from "mod";"#,
    r#"export type{default as"a-b"}from"mod";"#,
  );
}

#[test]
fn export_type_string_name_can_be_aliased_as_default() {
  roundtrip(
    r#"export type { "a-b" as default } from "mod";"#,
    r#"export type{"a-b"as default}from"mod";"#,
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
fn keyword_import_name_requires_as() {
  roundtrip(
    "import { while as w } from \"x\";",
    "import{while as w}from\"x\";",
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
