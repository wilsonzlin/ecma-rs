use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};

#[test]
fn hir_emits_undefined_identifier() {
  let lowered = lower_from_source_with_kind(FileKind::Js, "undefined;").expect("lower");
  let emitted = emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit");
  assert_eq!(emitted, "undefined;");
}

#[test]
fn hir_preserves_undefined_in_member_expressions() {
  let lowered = lower_from_source_with_kind(FileKind::Js, "undefined.toString();").expect("lower");
  let emitted = emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit");
  assert_eq!(emitted, "undefined.toString();");
}

#[test]
fn hir_parenthesizes_void_0_in_member_expressions() {
  let lowered = lower_from_source_with_kind(FileKind::Js, "(void 0).toString();").expect("lower");
  let emitted = emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit");
  assert_eq!(emitted, "(void 0).toString();");
}

#[test]
fn hir_preserves_empty_export_from_statements() {
  let lowered =
    lower_from_source_with_kind(FileKind::Js, r#"export {} from "./side";"#).expect("lower");
  let emitted = emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit");
  assert_eq!(emitted, r#"export{}from"./side";"#);
}
