use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn use_define_for_class_fields_controls_used_before_initialization_diagnostic() {
  let source = r#"
class C {
  foo = this.bar;
  constructor(public bar: number) {}
}
"#;

  let key = FileKey::new("main.ts");

  let mut opts_define = CompilerOptions::default();
  opts_define.target = ScriptTarget::EsNext;
  opts_define.use_define_for_class_fields = true;
  let mut host_define = MemoryHost::with_options(opts_define);
  host_define.insert(key.clone(), source);
  let program_define = Program::new(host_define, vec![key.clone()]);
  let diagnostics_define = program_define.check();
  assert!(
    diagnostics_define
      .iter()
      .any(|diag| diag.code.as_str() == codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected diagnostics to include PROPERTY_USED_BEFORE_INITIALIZATION; got {diagnostics_define:#?}"
  );

  let mut opts_set = CompilerOptions::default();
  opts_set.target = ScriptTarget::EsNext;
  opts_set.use_define_for_class_fields = false;
  let mut host_set = MemoryHost::with_options(opts_set);
  host_set.insert(key.clone(), source);
  let program_set = Program::new(host_set, vec![key]);
  let diagnostics_set = program_set.check();
  assert!(
    diagnostics_set
      .iter()
      .all(|diag| diag.code.as_str() != codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected diagnostics to omit PROPERTY_USED_BEFORE_INITIALIZATION when use_define_for_class_fields is false; got {diagnostics_set:#?}"
  );
}

#[test]
fn use_define_for_class_fields_controls_inherited_property_used_before_initialization() {
  let source = r#"
class Base {
  x = 1;
}

class Derived extends Base {
  y = this.x;
  x = 2;
}
"#;

  let key = FileKey::new("main.ts");

  let mut opts_define = CompilerOptions::default();
  opts_define.target = ScriptTarget::Es2020;
  opts_define.use_define_for_class_fields = true;
  let mut host_define = MemoryHost::with_options(opts_define);
  host_define.insert(key.clone(), source);
  let program_define = Program::new(host_define, vec![key.clone()]);
  let diagnostics_define = program_define.check();
  assert!(
    diagnostics_define
      .iter()
      .any(|diag| diag.code.as_str() == codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected diagnostics to include PROPERTY_USED_BEFORE_INITIALIZATION; got {diagnostics_define:#?}"
  );

  let mut opts_set = CompilerOptions::default();
  opts_set.target = ScriptTarget::Es2020;
  opts_set.use_define_for_class_fields = false;
  let mut host_set = MemoryHost::with_options(opts_set);
  host_set.insert(key.clone(), source);
  let program_set = Program::new(host_set, vec![key]);
  let diagnostics_set = program_set.check();
  assert!(
    diagnostics_set
      .iter()
      .all(|diag| diag.code.as_str() != codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected diagnostics to omit PROPERTY_USED_BEFORE_INITIALIZATION when use_define_for_class_fields is false; got {diagnostics_set:#?}"
  );
}

#[test]
fn use_define_for_class_fields_controls_inherited_method_used_before_initialization() {
  let source = r#"
class Base {
  x() { return 1; }
}

class Derived extends Base {
  y = this.x;
  x = 2;
}
"#;

  let key = FileKey::new("main.ts");

  let mut opts_define = CompilerOptions::default();
  opts_define.target = ScriptTarget::Es2020;
  opts_define.use_define_for_class_fields = true;
  let mut host_define = MemoryHost::with_options(opts_define);
  host_define.insert(key.clone(), source);
  let program_define = Program::new(host_define, vec![key.clone()]);
  let diagnostics_define = program_define.check();
  assert!(
    diagnostics_define
      .iter()
      .any(|diag| diag.code.as_str() == codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected diagnostics to include PROPERTY_USED_BEFORE_INITIALIZATION; got {diagnostics_define:#?}"
  );

  let mut opts_set = CompilerOptions::default();
  opts_set.target = ScriptTarget::Es2020;
  opts_set.use_define_for_class_fields = false;
  let mut host_set = MemoryHost::with_options(opts_set);
  host_set.insert(key.clone(), source);
  let program_set = Program::new(host_set, vec![key]);
  let diagnostics_set = program_set.check();
  assert!(
    diagnostics_set
      .iter()
      .all(|diag| diag.code.as_str() != codes::PROPERTY_USED_BEFORE_INITIALIZATION.as_str()),
    "expected diagnostics to omit PROPERTY_USED_BEFORE_INITIALIZATION when use_define_for_class_fields is false; got {diagnostics_set:#?}"
  );
}
