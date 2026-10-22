use std::sync::Arc;

mod common;

use diagnostics::TextRange;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

/// `{ (x: string): number, a: "" } & { a: number }` is `never` → TS2349 on callee.
#[test]
fn never_intersection_not_callable_on_callee_span() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    no_implicit_any: false,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "declare const f: { (x: string): number, a: \"\" } & { a: number }\nf()\n";
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file");
  let diagnostics = program.check();
  let hits: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::NO_OVERLOAD.as_str())
    .collect();
  assert_eq!(
    hits.len(),
    1,
    "expected one not-callable, got {diagnostics:?}"
  );
  let d = hits[0];
  let start = source.rfind('f').expect("f") as u32;
  let end = start + 1;
  assert_eq!(d.primary.file, file_id);
  assert_eq!(
    d.primary.range,
    TextRange::new(start, end),
    "tsc TS2349 is on callee `f`, got {:?}: {}",
    d.primary.range,
    d.message
  );
}

/// Discriminant conflict `A & B` reduces to `never`; `ab.kind` is TS2339.
#[test]
fn alias_intersection_with_conflicting_discriminant_is_never() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    no_implicit_any: false,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = concat!(
    "type A = { kind: 'a', foo: string };\n",
    "type B = { kind: 'b', foo: number };\n",
    "declare let ab: A & B;\n",
    "ab.kind;\n",
  );
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file");
  let diagnostics = program.check();
  let hits: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::PROPERTY_DOES_NOT_EXIST.as_str())
    .collect();
  assert_eq!(
    hits.len(),
    1,
    "expected TS2339 on ab.kind when A&B is never, got {diagnostics:?}"
  );
  let kind_start = source.rfind("kind").expect("kind") as u32;
  let kind_end = kind_start + 4;
  assert_eq!(hits[0].primary.file, file_id);
  assert_eq!(hits[0].primary.range, TextRange::new(kind_start, kind_end));
}

/// Write-indexed-access: `obj[k]` with `k: 'a'|'b'` is `T['a'] & T['b']`.
/// Conflicting property types reduce to `never`; `any` is not assignable (TS2322).
#[test]
fn union_key_indexed_write_to_never_rejects_any() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    no_implicit_any: false,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = concat!(
    "const x1 = { a: 'foo', b: 42 };\n",
    "declare let k: 'a' | 'b';\n",
    "x1[k] = 'bar' as any;\n",
  );
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file");
  let diagnostics = program.check();
  let hits: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert_eq!(
    hits.len(),
    1,
    "expected TS2322 for any ↛ never write target, got {diagnostics:?}"
  );
  let start = source.find("x1[k]").expect("x1[k]") as u32;
  let end = start + "x1[k]".len() as u32;
  assert_eq!(hits[0].primary.file, file_id);
  assert_eq!(hits[0].primary.range, TextRange::new(start, end));
}

/// Bare `never` property access is TS2339 (tsc reportNonexistentProperty).
#[test]
fn never_property_access_is_ts2339() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "declare let x: never;\nx.foo;\n";
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::PROPERTY_DOES_NOT_EXIST.as_str()),
    "expected TS2339 on never.foo, got {diagnostics:?}"
  );
}

/// tsc: `any` is not assignable to `never` (TS2322).
#[test]
fn any_not_assignable_to_never() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    no_implicit_any: false,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "declare let n: never;\nn = 0 as any;\n";
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected TS2322 for any ↛ never, got {diagnostics:?}"
  );
}
