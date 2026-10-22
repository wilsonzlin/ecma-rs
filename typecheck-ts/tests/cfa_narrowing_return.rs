//! Regression: CFA typeof-narrowing return inference via primitive interface
//! members (`string.length`, `number.toFixed`) — cornerstone `cfa_narrowing`.

mod common;

use std::sync::Arc;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn typeof_narrow_return_unions_primitive_interface_members() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    strict_null_checks: true,
    ..CompilerOptions::default()
  });
  let file = FileKey::new("cfa_narrowing.ts");
  host.insert(
    file.clone(),
    Arc::from(
      r#"
export function typeofNarrow(x: string | number) {
  if (typeof x === "string") {
    return x.length;
  }
  return x.toFixed(1);
}
export function discriminant(
  shape: { kind: "square"; size: number } | { kind: "circle"; radius: number },
) {
  if (shape.kind === "square") {
    return shape.size;
  }
  return shape.radius;
}
"#
      .to_string(),
    ),
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();
  let file_id = program.file_id(&file).expect("file id");

  let typeof_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("typeofNarrow"))
    .expect("typeofNarrow");
  let rendered = program
    .display_type(program.type_of_def(typeof_def))
    .to_string();
  assert!(
    rendered == "(number | string) => number | string"
      || rendered == "(string | number) => string | number"
      || rendered == "(number | string) => string | number"
      || rendered == "(string | number) => number | string",
    "expected typeofNarrow return union number|string from narrowed .length/.toFixed, got {rendered}"
  );

  let disc_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("discriminant"))
    .expect("discriminant");
  let disc = program
    .display_type(program.type_of_def(disc_def))
    .to_string();
  assert!(
    disc.contains("=> number"),
    "expected discriminant => number, got {disc}"
  );
}

#[test]
fn unannotated_string_param_length_infers_number_return() {
  let mut host = MemoryHost::with_options(CompilerOptions::default());
  let file = FileKey::new("f.ts");
  host.insert(
    file.clone(),
    Arc::from("function f(x: string) { return x.length; }\n"),
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();
  let file_id = program.file_id(&file).expect("file id");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("f"))
    .expect("f");
  let rendered = program.display_type(program.type_of_def(def)).to_string();
  assert_eq!(rendered, "(string) => number");
}
