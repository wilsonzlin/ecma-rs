//! Residual privateNames: dual generic instantiation + construct inference.

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn check_with(opts: CompilerOptions, src: &str) -> Vec<(String, String)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let text = src.to_string();
  program
    .check()
    .into_iter()
    .map(|d| {
      let snip = text
        .get(d.primary.range.start as usize..d.primary.range.end as usize)
        .unwrap_or("")
        .to_string();
      (d.code.as_str().to_string(), snip)
    })
    .collect()
}

fn strip_directives(src: &str) -> String {
  src
    .lines()
    .filter(|l| !l.trim_start().starts_with("// @"))
    .collect::<Vec<_>>()
    .join("\n")
}

#[test]
fn computed_property_name3_no_false_ts18013() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::EsNext;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNameComputedPropertyName3.ts"
  ));
  let diags = check_with(opts, &src);
  assert!(
    !diags.iter().any(|(c, _)| c == "TS18013"),
    "false TS18013: {diags:?}"
  );
}

#[test]
fn when_not_use_define_full_clean() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::EsNext;
  opts.use_define_for_class_fields = false;
  opts.strict_null_checks = true;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNameWhenNotUseDefineForClassFieldsInEsNext.ts"
  ));
  let diags = check_with(opts, &src);
  assert!(diags.is_empty(), "{diags:?}");
}

#[test]
fn constructor_chain_2_only_ts2339() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNamesConstructorChain-2.ts"
  ));
  let diags = check_with(opts, &src);
  assert_eq!(
    diags.iter().map(|(c, _)| c.as_str()).collect::<Vec<_>>(),
    vec!["TS2339"],
    "{diags:?}"
  );
  assert_eq!(diags[0].1, "#bar");
}

#[test]
fn and_generic_classes_2_exact_tsc() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.strict_function_types = true;
  opts.strict_property_initialization = true;
  opts.use_define_for_class_fields = true;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNamesAndGenericClasses-2.ts"
  ));
  let diags = check_with(opts, &src);
  let codes: Vec<&str> = diags.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(
    codes,
    vec!["TS18013", "TS2322", "TS2322"],
    "exact tsc codes: {diags:?}"
  );
  assert_eq!(diags[0].1, "#foo");
  assert_eq!(diags[1].1, "a");
  assert_eq!(diags[2].1, "b");
}

#[test]
fn in_generic_classes_exact_tsc() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.strict_function_types = true;
  opts.strict_property_initialization = false;
  opts.use_define_for_class_fields = true;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNamesInGenericClasses.ts"
  ));
  let diags = check_with(opts, &src);
  let codes: Vec<&str> = diags.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(
    codes,
    vec!["TS18013", "TS18013", "TS18013", "TS2322", "TS2322"],
    "exact tsc codes: {diags:?}"
  );
  assert!(diags.iter().take(3).all(|(_, s)| s.starts_with('#')));
  assert_eq!(diags[3].1, "a");
  assert_eq!(diags[4].1, "b");
}

#[test]
fn dual_instantiation_private_lookup_and_assign() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.strict_function_types = true;
  opts.strict_property_initialization = false;
  opts.use_define_for_class_fields = true;
  let src = r#"
class C<T> {
  #foo: T;
  m1(x: C<number>) { return x.#foo; }
  m2(x: C<string>) { return x.#foo; }
}
declare let a: C<number>;
declare let b: C<string>;
a.#foo;
a = b;
b = a;
"#;
  let diags = check_with(opts, src);
  assert!(
    !diags.iter().any(|(c, _)| c == "TS2339"),
    "false TS2339 on dual instantiation: {diags:?}"
  );
  let codes: Vec<&str> = diags.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(codes, vec!["TS18013", "TS2322", "TS2322"], "{diags:?}");
}

#[test]
fn generic_construct_widens_literal_type_arg() {
  // `new C(3)` must infer `C<number>` (not `C<3>`) so `a.foo = 5` is OK.
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  let src = r#"
class C<T> {
  foo: T;
  constructor(t: T) { this.foo = t; }
  set baz(t: T) { this.foo = t; }
  get baz(): T { return this.foo; }
}
let a = new C(3);
a.foo = 5;
a.baz = 5;
const x: number = a.baz;
"#;
  let diags = check_with(opts, src);
  assert!(diags.is_empty(), "{diags:?}");
}

#[test]
fn failed_assignment_keeps_declared_binding_type() {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  let src = r#"
declare let a: { foo: number };
declare let b: { foo: string };
a = b;
b = a;
"#;
  let diags = check_with(opts, src);
  let assigns: Vec<_> = diags
    .iter()
    .filter(|(c, _)| c == "TS2322")
    .map(|(_, s)| s.as_str())
    .collect();
  assert_eq!(assigns, vec!["a", "b"], "{diags:?}");
}

#[test]
fn indexed_access_private_hash_string_is_ts2339() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.strict_property_initialization = false;
  let src = r##"
class C {
  foo = 3;
  #bar = 3;
  constructor () {
    const ok: C["foo"] = 3;
    const badAlways: C["#bar"] = 3;
  }
}
"##;
  let diags = check_with(opts, src);
  assert!(
    diags
      .iter()
      .any(|(c, s)| c == "TS2339" && s.contains("#bar")),
    "expected TS2339 on \"#bar\": {diags:?}"
  );
}

#[test]
fn computed_key_comma_arrow_parses_ts2454() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNameComputedPropertyName2.ts"
  ));
  let diags = check_with(opts, &src);
  assert_eq!(
    diags.iter().map(|(c, _)| c.as_str()).collect::<Vec<_>>(),
    vec!["TS2454"],
    "{diags:?}"
  );
  assert_eq!(diags[0].1, "getX");
}

#[test]
fn indexed_access_private_recovery_exact_tsc() {
  let mut opts = CompilerOptions::default();
  opts.target = ScriptTarget::Es2015;
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.strict_function_types = true;
  opts.strict_property_initialization = false;
  opts.use_define_for_class_fields = true;
  let src = strip_directives(include_str!(
    "../../parse-js/tests/TypeScript/tests/cases/conformance/classes/members/privateNames/privateNamesAndIndexedAccess.ts"
  ));
  let diags = check_with(opts, &src);
  let codes: Vec<&str> = diags.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(
    codes,
    vec!["PS0013", "TC3000", "PS0013", "PS0031", "PS0031", "TS2339"],
    "exact tsc-aligned codes: {diags:?}"
  );
  assert_eq!(diags[0].1, "#bar");
  assert_eq!(diags[1].1, "#bar");
  assert_eq!(diags[5].1, "\"#bar\"");
}
