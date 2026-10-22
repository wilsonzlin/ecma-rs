//! JS "expando" property-assignment namespace members (tsc
//! `bindSpecialPropertyAssignment`).
//!
//! In `.js` files under allowJs+checkJs, `Outer.X = <class|function>` and
//! `Outer.X.prototype = <object literal>` register `X` in the outer's
//! value+type namespaces. Expando bases (tsc `bindSpecialPropertyAssignment`):
//! `var Outer = {}`, `var Outer = function … {}`, `function Outer() {}`,
//! `var Outer = class … {}`, and `var Outer = (…) => …`.
//! `new Outer.X()`, `Outer.X` member access, and JSDoc `@type {Outer.X}`
//! (instance type) all resolve. Covers conformance
//! `salsa/typeFromPropertyAssignment.ts`,
//! `salsa/typeFromPropertyAssignment24.ts`,
//! `salsa/typeFromPropertyAssignment2.ts`,
//! `salsa/typeFromPropertyAssignment3.ts`, and
//! `jsdoc/jsdocTypeReferenceToMergedClass.ts`.

mod common;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileKey, Host, HostError, MemoryHost, Program};

struct JsHost {
  inner: MemoryHost,
}

impl JsHost {
  fn new() -> Self {
    let mut options = CompilerOptions::default();
    options.no_default_lib = true;
    options.no_implicit_any = false;
    options.check_js = Some(true);
    let mut inner = MemoryHost::with_options(options);
    inner.add_lib(common::core_globals_lib());
    Self { inner }
  }

  fn insert(&mut self, key: FileKey, source: &str) {
    self.inner.insert(key, source);
  }
}

impl Host for JsHost {
  fn file_text(&self, file: &FileKey) -> Result<std::sync::Arc<str>, HostError> {
    self.inner.file_text(file)
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    self.inner.resolve(from, specifier)
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.inner.compiler_options()
  }

  fn lib_files(&self) -> Vec<typecheck_ts::lib_support::LibFile> {
    self.inner.lib_files()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    let kind = self.inner.file_kind(file);
    if file.as_str().ends_with(".js") {
      assert_eq!(kind, FileKind::Js, "fixture paths should be .js");
    }
    kind
  }
}

const CASE_A_USAGE: &str = r#"Outer.Inner.Message = function() {
};

var y = new Outer.Inner()
y.name
/** @type {Outer.Inner} should be instance type, not static type */
var x;
x.name
"#;

const CASE_A_DEF: &str = r#"var Outer = {}
Outer.Inner = class {
  name() {
    return 'hi'
  }
}
"#;

const CASE_B: &str = r#"var Workspace = {}
/** @type {Workspace.Project} */
var p;
p.isServiceProject()

Workspace.Project = function wp() { }
Workspace.Project.prototype = {
  isServiceProject() {}
}
"#;

#[test]
fn class_rhs_cross_file_value_and_jsdoc_type() {
  let mut host = JsHost::new();
  let usage = FileKey::new("usage.js");
  let def = FileKey::new("def.js");
  // usage first in compilation, as in the conformance case.
  host.insert(usage.clone(), CASE_A_USAGE);
  host.insert(def.clone(), CASE_A_DEF);
  let program = Program::new(host, vec![usage.clone(), def.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "no TS2694 expected for @type {{Outer.Inner}}; got {diagnostics:?}"
  );
  // tsc reports only TS2454 (`x` used before assigned).
  let unexpected: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected.is_empty(),
    "only TS2454 expected (tsc parity); got {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::USE_BEFORE_ASSIGNMENT.as_str()),
    "expected TS2454 on `x`; got {diagnostics:?}"
  );

  let usage_id = program.file_id(&usage).expect("usage file id");
  // `new Outer.Inner()` yields the class instance type; `y.name` resolves.
  let y_name_offset = CASE_A_USAGE.find("y.name").expect("y.name") as u32 + 2;
  let name_ty = program
    .type_at(usage_id, y_name_offset)
    .expect("type for y.name");
  assert_eq!(program.display_type(name_ty).to_string(), "() => string");

  // `@type {Outer.Inner}` is the *instance* type, not the static side:
  // `x.name` resolves to the instance method (alongside the expected TS2454).
  let x_name_offset = CASE_A_USAGE.find("x.name").expect("x.name") as u32 + 2;
  let x_name_ty = program
    .type_at(usage_id, x_name_offset)
    .expect("type for x.name");
  assert_eq!(program.display_type(x_name_ty).to_string(), "() => string");
}

#[test]
fn function_rhs_with_prototype_is_js_constructor() {
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  let src = format!("{CASE_B}var n = new Workspace.Project();\nn.isServiceProject();\n");
  host.insert(key.clone(), &src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  // tsc parity: the only diagnostic under `--strictNullChecks` is TS2454 for
  // the unassigned `var p;` (with strictNullChecks off tsc reports nothing).
  // Crucially the call itself checks clean — no TS2694/TS2339/TS2322.
  let unexpected: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected.is_empty(),
    "only TS2454 (unassigned `var p;`) is allowed here; got {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  // `@type {Workspace.Project}` = the prototype instance type.
  let member_offset = src.find("p.isServiceProject").expect("p.isServiceProject") as u32 + 2;
  let member_ty = program
    .type_at(file_id, member_offset)
    .expect("type for p.isServiceProject");
  assert_eq!(program.display_type(member_ty).to_string(), "() => void");

  // `new Workspace.Project()` = the instance type.
  let n_offset = src.find("var n =").expect("var n") as u32 + 4;
  let n_ty = program.type_at(file_id, n_offset).expect("type for n");
  assert_eq!(
    program.display_type(n_ty).to_string(),
    "{ isServiceProject: () => void }"
  );
}

#[test]
fn class_rhs_single_file() {
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  let src = r#"var Outer = {}
Outer.Inner = class {
  name() { return 'hi' }
}
var y = new Outer.Inner()
y.name
/** @type {Outer.Inner} */
var x;
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "single-file class RHS expando should check clean; got {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let y_name_offset = src.find("y.name").expect("y.name") as u32 + 2;
  let name_ty = program
    .type_at(file_id, y_name_offset)
    .expect("type for y.name");
  assert_eq!(program.display_type(name_ty).to_string(), "() => string");
}

#[test]
fn class_expression_and_arrow_bases_are_expando_containers() {
  // tsc `bindSpecialPropertyAssignment` treats `var Outer = class … {}` and
  // `var Outer = (…) => …` as expando containers too
  // (`salsa/typeFromPropertyAssignment.ts`): `Outer.Inner = class …` resolves
  // in value *and* JSDoc-type positions.
  let src = r#"var Outer = class O {
    m(x, y) { }
}
Outer.Inner = class I {
    n(a, b) { }
}
/** @type {Outer} */
var si
si.m
/** @type {Outer.Inner} */
var oi
oi.n
"#;
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  // tsc reports TS2454 for the unassigned `si`/`oi` under --strict (the
  // conformance case runs non-strict); everything else must be clean.
  let unexpected: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected.is_empty(),
    "class-expression base expando should check clean modulo TS2454; got {diagnostics:?}"
  );

  let arrow = r#"var OuterA = (x) => x
OuterA.Inner = class I2 {
    n(a) { return a; }
}
var inst = new OuterA.Inner(1);
/** @type {OuterA.Inner} */
var oia
oia.n
"#;
  let mut host2 = JsHost::new();
  let key2 = FileKey::new("arrow.js");
  host2.insert(key2.clone(), arrow);
  let program2 = Program::new(host2, vec![key2.clone()]);
  let diagnostics2 = program2.check();
  let unexpected2: Vec<_> = diagnostics2
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected2.is_empty(),
    "arrow base expando should check clean modulo TS2454; got {diagnostics2:?}"
  );
}

#[test]
fn members_from_multiple_files_merge_on_the_global_outer() {
  let mut host = JsHost::new();
  let a = FileKey::new("a.js");
  let b = FileKey::new("b.js");
  let use_ = FileKey::new("use.js");
  host.insert(
    a.clone(),
    "var Outer = {}\nOuter.A = class { m() { return 1 } }\n",
  );
  host.insert(
    b.clone(),
    "Outer.B = function b() {}\nOuter.B.prototype = { svc() {} }\n",
  );
  host.insert(
    use_.clone(),
    "var a = new Outer.A()\na.m\nvar s = new Outer.B()\ns.svc()\n",
  );
  let program = Program::new(host, vec![a.clone(), b.clone(), use_.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "members from all files should merge onto the global `Outer`; got {diagnostics:?}"
  );

  let use_id = program.file_id(&use_).expect("use file id");
  let src = "var a = new Outer.A()\na.m\nvar s = new Outer.B()\ns.svc()\n";
  let a_ty = program
    .type_at(use_id, src.find("var a").unwrap() as u32 + 4)
    .expect("type of a");
  assert_eq!(
    program.display_type(a_ty).to_string(),
    "{ m: () => number }"
  );
  let s_ty = program
    .type_at(use_id, src.find("var s").unwrap() as u32 + 4)
    .expect("type of s");
  assert_eq!(
    program.display_type(s_ty).to_string(),
    "{ svc: () => void }"
  );
}

#[test]
fn function_member_without_prototype_is_plain_callable() {
  // tsc: `obj.method = function (hunch) { return true; }` (no `.prototype`
  // assignment) registers a plain callable member — `obj.method()` checks and
  // infers the return (conformance `typeFromPropertyAssignment7.ts`).
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  let src = r#"var obj = {};
obj.method = function (hunch) {
    return true;
}
var b = obj.method();
/** @type {obj.method} */
var m;
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  let unexpected: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected.is_empty(),
    "plain function member call should check clean; got {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let b_ty = program
    .type_at(file_id, src.find("var b").unwrap() as u32 + 4)
    .expect("type for b");
  assert_eq!(program.display_type(b_ty).to_string(), "boolean");
}

#[test]
fn ts_files_do_not_register_expando_members() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.no_implicit_any = false;
  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  let key = FileKey::new("main.ts");
  let src = r#"var Outer = {}
Outer.X = 1;
var y = Outer.X;
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  let file_id = program.file_id(&key).expect("file id");
  let defs = program.definitions_in_file(file_id);
  let outer_def = defs
    .iter()
    .copied()
    .find(|d| program.def_name(*d).as_deref() == Some("Outer"))
    .expect("Outer def");
  let outer_ty = program.type_of_def(outer_def);
  assert_eq!(
    program.display_type(outer_ty).to_string(),
    "{}",
    "TS files must not grow expando members; diagnostics: {diagnostics:?}"
  );
}

#[test]
fn non_empty_object_initializer_is_not_expando() {
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  let src = r#"var Outer = { a: 1 }
Outer.Inner = class {}
/** @type {Outer.Inner} */
var x;
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "non-{{}} initializer must not be treated as expando (TS2694 stays); got {diagnostics:?}"
  );
}

#[test]
fn jsdoc_annotated_var_is_not_expando() {
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  let src = r#"/** @type {Object} */
var Outer = {}
Outer.Inner = class {}
/** @type {Outer.Inner} */
var x;
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "annotated vars are not expando (TS2694 stays); got {diagnostics:?}"
  );
}

#[test]
fn function_expr_var_is_expando_base() {
  // `salsa/typeFromPropertyAssignment3.ts`: `var Outer = function O() {…}` is
  // an expando container (tsc `bindSpecialPropertyAssignment`), so
  // `Outer.Inner = class …` resolves in value *and* JSDoc-type positions.
  let mut host = JsHost::new();
  let key = FileKey::new("a.js");
  let src = r#"var Outer = function O() {
    this.y = 2
}
Outer.Inner = class I {
    constructor() {
        this.x = 1
    }
}
/** @type {Outer} */
var ja
ja.y
/** @type {Outer.Inner} */
var da
da.x
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "no TS2694 expected for @type {{Outer.Inner}} on a function base; got {diagnostics:?}"
  );
  // tsc reports only TS2454 (`ja` / `da` used before assigned).
  let unexpected: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected.is_empty(),
    "only TS2454 expected (tsc parity); got {diagnostics:?}"
  );
}

#[test]
fn function_declaration_is_expando_base() {
  // `salsa/typeFromPropertyAssignment2.ts`: `function Outer() {}` is an
  // expando container (tsc `bindSpecialPropertyAssignment`), so
  // `Outer.Inner = class …` resolves in value *and* JSDoc-type positions.
  let mut host = JsHost::new();
  let key = FileKey::new("a.js");
  let src = r#"function Outer() {
    this.y = 2
}
Outer.Inner = class I {
    constructor() {
        this.x = 1
    }
}
/** @type {Outer} */
var ok
ok.y
/** @type {Outer.Inner} */
var oc
oc.x
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "no TS2694 expected for a function-declaration base; got {diagnostics:?}"
  );
  // tsc reports only TS2454 (`ok` / `oc` used before assigned).
  let unexpected: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() != codes::USE_BEFORE_ASSIGNMENT.as_str())
    .collect();
  assert!(
    unexpected.is_empty(),
    "only TS2454 expected (tsc parity); got {diagnostics:?}"
  );
}

#[test]
fn arrow_function_var_is_expando_base() {
  // tsc `bindSpecialPropertyAssignment`: arrow-function vars ARE expando
  // containers in JS — `@type {Outer.Inner}` resolves (verified against tsc
  // 5.9.3; an earlier revision of this test asserted the opposite from a
  // misread of tsc's behavior).
  let mut host = JsHost::new();
  let key = FileKey::new("mod.js");
  let src = r#"var Outer = () => {}
Outer.Inner = class {}
/** @type {Outer.Inner} */
var x;
"#;
  host.insert(key.clone(), src);
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NAMESPACE_NO_EXPORTED_MEMBER.as_str()),
    "arrow-function vars are expando bases (no TS2694); got {diagnostics:?}"
  );
}
