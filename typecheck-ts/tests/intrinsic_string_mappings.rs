use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn intrinsic_string_mappings_evaluate_literals_and_unions() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.include_dom = false;

  let mut host = MemoryHost::with_options(options);
  host.add_lib(LibFile {
    key: FileKey::new("lib.d.ts"),
    name: Arc::from("lib.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
type Uppercase<S extends string> = intrinsic;
type Lowercase<S extends string> = intrinsic;
type Capitalize<S extends string> = intrinsic;
type Uncapitalize<S extends string> = intrinsic;
"#,
    ),
  });

  let entry = FileKey::new("a.ts");
  let source = r#"
type Loud = Uppercase<"hello">;
type Mixed = Uppercase<"a" | "b">;
type Capital = Capitalize<"hello">;
type Uncapital = Uncapitalize<"Hello">;

const ok: Loud = "HELLO";
const bad: Loud = "hello";

const ok2: Mixed = "A";
const bad2: Mixed = "C";

const ok3: Capital = "Hello";
const bad3: Capital = "hello";

const ok4: Uncapital = "hello";
const bad4: Uncapital = "Hello";
"#;

  host.insert(entry.clone(), Arc::from(source));
  let program = Program::new(host, vec![entry.clone()]);

  let diagnostics = program.check();
  let mismatch_count = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .count();
  assert_eq!(
    mismatch_count, 4,
    "expected four intrinsic mapping assignment errors; got {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("entry file id");
  let loud_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Loud"))
    .expect("type alias Loud def");
  let loud_ty = program.type_of_def(loud_def);
  assert_eq!(program.display_type(loud_ty).to_string(), "\"HELLO\"");

  let loud_value_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("ok"))
    .expect("var ok def");
  let loud_value_ty = program.type_of_def(loud_value_def);
  assert_eq!(program.display_type(loud_value_ty).to_string(), "\"HELLO\"");

  let mixed_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Mixed"))
    .expect("type alias Mixed def");
  let mixed_ty = program.type_of_def(mixed_def);
  assert_eq!(program.display_type(mixed_ty).to_string(), "\"A\" | \"B\"");

  let mixed_value_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("ok2"))
    .expect("var ok2 def");
  let mixed_value_ty = program.type_of_def(mixed_value_def);
  assert_eq!(
    program.display_type(mixed_value_ty).to_string(),
    "\"A\" | \"B\""
  );
}
