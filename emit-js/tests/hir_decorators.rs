use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn assert_hir_decorator_roundtrip(source: &str, expected_substrings: &[&str]) {
  let lowered = lower_from_source_with_kind(FileKind::Ts, source)
    .unwrap_or_else(|err| panic!("failed to lower {source}: {err:?}"));

  let options = [EmitOptions::default(), EmitOptions::minified()];
  for opts in options {
    let emitted1 = emit_hir_file_to_string(&lowered, opts).expect("emit first pass");
    let emitted2 = emit_hir_file_to_string(&lowered, opts).expect("emit second pass");
    assert_eq!(emitted1, emitted2, "HIR emission must be deterministic");

    for needle in expected_substrings {
      assert!(
        emitted1.contains(needle),
        "expected emitted output to contain {needle:?}\nsource:\n{source}\nemitted:\n{emitted1}"
      );
    }

    parse_with_options(
      &emitted1,
      ParseOptions {
        dialect: Dialect::Ts,
        source_type: SourceType::Module,
      },
    )
    .expect("decorator output should parse as TS");

    let lowered_roundtrip =
      lower_from_source_with_kind(FileKind::Ts, &emitted1).unwrap_or_else(|err| {
        panic!("failed to lower emitted output: {err:?}\nemitted:\n{emitted1}")
      });
    let emitted_roundtrip =
      emit_hir_file_to_string(&lowered_roundtrip, opts).expect("emit roundtrip pass");
    assert_eq!(
      emitted1, emitted_roundtrip,
      "emitting after re-lowering must be stable"
    );
  }
}

#[test]
fn hir_emits_class_decorators_before_export() {
  assert_hir_decorator_roundtrip("@dec\nexport class C {}", &["@dec export class C"]);
}

#[test]
fn hir_emits_class_member_decorators() {
  assert_hir_decorator_roundtrip("class C { @dec method(){} }", &["@dec method"]);
}

#[test]
fn hir_emits_parameter_decorators() {
  assert_hir_decorator_roundtrip("class C { method(@dec x: any){} }", &["(@dec x"]);
}
