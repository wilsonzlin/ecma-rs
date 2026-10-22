//! Namespace-nested interfaces merge across declarations — including across
//! files (cross-file lib augmentation: `Intl.PluralRulesConstructor` is
//! declared in both `lib.es2018.intl` and `lib.es2020.intl` and tsc merges
//! them into one overload set). Nested defs carry no semantic symbols, so the
//! merge groups by (canonical namespace def, name) in `ensure_interned_types`.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn check2(f1: &str, f2: &str, f3: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
  let a = FileKey::new("a.d.ts");
  let b = FileKey::new("b.d.ts");
  let u = FileKey::new("use.ts");
  host.insert(a.clone(), f1);
  host.insert(b.clone(), f2);
  host.insert(u.clone(), f3);
  let program = Program::new(host, vec![a, b, u]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn cross_file_namespace_interface_merge() {
  let diagnostics = check2(
    "declare namespace N {\n  interface Ctor {\n    new (x: string): Object;\n  }\n  const P: Ctor;\n}",
    "declare namespace N {\n  interface Ctor {\n    new (x: number): Object;\n  }\n}",
    "const a = new N.P('s');\nconst b = new N.P(1);",
  );
  assert!(
    diagnostics.is_empty(),
    "expected both overloads after merge; got {diagnostics:?}"
  );
}

#[test]
fn cross_file_intl_style_constructor_merge() {
  // Mirror of the es2018/es2020 `PluralRulesConstructor` augmentation: the
  // later declaration's wider parameter type must be part of the merged
  // overload set (object literal and array forms both resolve).
  let diagnostics = check2(
    "declare namespace Intl {\n  interface PluralRulesConstructor {\n    new (locales?: string | readonly string[]): object;\n  }\n  const PluralRules: PluralRulesConstructor;\n}",
    "declare namespace Intl {\n  type LocalesArgument = string | object | readonly (string | object)[] | undefined;\n  interface PluralRulesConstructor {\n    new (locales?: LocalesArgument): object;\n  }\n}",
    "declare const enUS: object;\nconst x = new Intl.PluralRules(enUS);\nconst y = new Intl.PluralRules([enUS]);",
  );
  assert!(
    diagnostics.is_empty(),
    "expected the es2020 overload to be visible after merge; got {diagnostics:?}"
  );
}

#[test]
fn same_file_nested_interface_merge() {
  // Two same-named interfaces inside one namespace also merge.
  let mut host = MemoryHost::default();
  let f = FileKey::new("n.d.ts");
  host.insert(
    f.clone(),
    "declare namespace N {\n  interface Ctor {\n    new (x: string): Object;\n  }\n  interface Ctor {\n    new (x: number): Object;\n  }\n  const P: Ctor;\n}",
  );
  let u = FileKey::new("use.ts");
  host.insert(u.clone(), "const a = new N.P('s');\nconst b = new N.P(1);");
  let program = Program::new(host, vec![f, u]);
  let diagnostics: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  assert!(
    diagnostics.is_empty(),
    "expected same-file nested interfaces to merge; got {diagnostics:?}"
  );
}
