use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn intrinsic_string_mappings_are_displayed_as_literals() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("a.ts");
  let source = r#"
export const upper: Uppercase<"hello"> = "HELLO";
export const lower: Lowercase<"HELLO"> = "hello";
export const capitalize: Capitalize<"hello"> = "Hello";
export const uncapitalize: Uncapitalize<"Hello"> = "hello";
export const union: Uppercase<"a" | "b"> = Math.random() > 0.5 ? "A" : "B";
export const template: Uppercase<`foo${string}bar`> = "FOOXBAR";
export const noInfer: NoInfer<"x"> = "x";
"#;
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let ty = |name: &str| {
    exports
      .get(name)
      .and_then(|entry| entry.type_id)
      .unwrap_or_else(|| panic!("missing type for export {name:?}"))
  };

  assert_eq!(program.display_type(ty("upper")).to_string(), "\"HELLO\"");
  assert_eq!(program.display_type(ty("lower")).to_string(), "\"hello\"");
  assert_eq!(
    program.display_type(ty("capitalize")).to_string(),
    "\"Hello\""
  );
  assert_eq!(
    program.display_type(ty("uncapitalize")).to_string(),
    "\"hello\""
  );
  assert_eq!(
    program.display_type(ty("union")).to_string(),
    "\"A\" | \"B\""
  );
  assert_eq!(
    program.display_type(ty("template")).to_string(),
    "`FOO${Uppercase<string>}BAR`"
  );
  assert_eq!(program.display_type(ty("noInfer")).to_string(), "\"x\"");
}
