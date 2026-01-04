use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, FileKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

#[test]
fn hir_emit_parse_lower_emit_is_stable() {
  let source = r#"
    @dec
    export class C {
      static x = undefined;
      y = undefined?.value ?? null;
      static {
        let z = undefined ?? 0;
      }
    }
    export {} from "./side";
  "#;

  let first_lowered = lower_from_source_with_kind(FileKind::Ts, source).expect("lower");
  let emit_opts = EmitOptions::minified();
  let emitted1 = emit_hir_file_to_string(&first_lowered, emit_opts).expect("emit");

  parse_with_options(
    &emitted1,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("emitted output should parse");

  let second_lowered = lower_from_source_with_kind(FileKind::Ts, &emitted1).expect("lower emitted");
  let emitted2 = emit_hir_file_to_string(&second_lowered, emit_opts).expect("re-emit");
  assert_eq!(emitted1, emitted2);
}
