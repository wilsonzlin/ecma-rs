//! Declaration merging: a same-name `interface` (TYPE namespace) and `var`
//! (VALUE namespace) inside a namespace must keep distinct types. The var's
//! annotation type must not pollute the interface's instance type — the
//! `lib.*.d.ts` `Intl.NumberFormat` pattern, where
//! `interface NumberFormat` and `var NumberFormat: NumberFormatConstructor`
//! coexist.

mod common;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn new_host() -> MemoryHost {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  host
}

const INTL_SRC: &str = r#"declare namespace Intl {
  interface NumberFormat {
    method(): void;
  }
  interface NumberFormatConstructor {
    readonly prototype: NumberFormat;
    new (x?: string): NumberFormat;
  }
  var NumberFormat: NumberFormatConstructor;
}
const i = new Intl.NumberFormat();
const v = Intl.NumberFormat;
const p = Intl.NumberFormat.prototype;
"#;

#[test]
fn construct_returns_instance_type_despite_var_name_collision() {
  let mut host = new_host();
  let file = FileKey::new("a.d.ts");
  host.insert(file.clone(), INTL_SRC);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let offset = INTL_SRC.find("new Intl.NumberFormat()").unwrap() as u32;
  let ty = program.type_at(file_id, offset).expect("type at new expr");
  assert_eq!(program.display_type(ty).to_string(), "NumberFormat");
}

#[test]
fn value_side_stays_constructor_interface() {
  let mut host = new_host();
  let file = FileKey::new("a.d.ts");
  host.insert(file.clone(), INTL_SRC);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let marker = "v = Intl.NumberFormat";
  let offset = INTL_SRC.find(marker).unwrap() as u32 + marker.len() as u32 - 1;
  let ty = program
    .type_at(file_id, offset)
    .expect("type at Intl.NumberFormat value");
  assert_eq!(
    program.display_type(ty).to_string(),
    "NumberFormatConstructor"
  );

  // The constructor's `prototype` property is declared as the instance
  // interface; the var's annotation must not rewrite it.
  let p_marker = "p = Intl.NumberFormat.prototype";
  let p_offset = INTL_SRC.find(p_marker).unwrap() as u32 + p_marker.len() as u32 - 1;
  let p_ty = program
    .type_at(file_id, p_offset)
    .expect("type at Intl.NumberFormat.prototype");
  assert_eq!(program.display_type(p_ty).to_string(), "NumberFormat");
}

#[test]
fn same_name_interface_and_var_keep_type_side() {
  let mut host = new_host();
  let file = FileKey::new("a.d.ts");
  let src = r#"interface X {
  a: string;
}
var X: { b: number };
declare const q: X;
const qa = q.a;
"#;
  host.insert(file.clone(), src);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let q_offset = src.find("q: X").unwrap() as u32;
  let q_ty = program.type_at(file_id, q_offset).expect("type at q");
  assert_eq!(program.display_type(q_ty).to_string(), "X");

  let qa_offset = src.find("q.a").unwrap() as u32 + 2;
  let qa_ty = program.type_at(file_id, qa_offset).expect("type at q.a");
  assert_eq!(program.display_type(qa_ty).to_string(), "string");
}
