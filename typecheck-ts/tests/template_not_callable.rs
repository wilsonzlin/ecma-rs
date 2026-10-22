use diagnostics::TextRange;
use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

/// `` `abc${0}abc`(…) `` — tsc TS2349 on the template callee (not silenced as unknown).
#[test]
fn template_literal_call_is_not_callable() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "`abc${0}abc`(`hello`);\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let not_callable: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::NO_OVERLOAD.as_str())
    .collect();
  assert_eq!(
    not_callable.len(),
    1,
    "expected TC2000 not-callable, got {diagnostics:?}"
  );
  let diag = not_callable[0];
  let start = source.find('`').expect("template start") as u32;
  let end = source.find("(`").expect("call paren") as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

/// `` stringTag `body` `` — tag is a string template; tsc TS2349 on the tag.
#[test]
fn template_literal_as_tagged_template_tag_is_not_callable() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "`tag` `body`;\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let not_callable: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::NO_OVERLOAD.as_str())
    .collect();
  assert_eq!(
    not_callable.len(),
    1,
    "expected TC2000 not-callable, got {diagnostics:?}"
  );
  let diag = not_callable[0];
  let start = 0u32;
  let end = "`tag`".len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

/// Constructable-only class used as a tag — tsc TS2349 on the class name.
#[test]
fn constructable_only_tagged_template_tag_is_not_callable() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "class CtorTag {}\nCtorTag `Hello`;\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let not_callable: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::NO_OVERLOAD.as_str())
    .collect();
  assert_eq!(
    not_callable.len(),
    1,
    "expected TC2000 not-callable, got {diagnostics:?}"
  );
  let diag = not_callable[0];
  let start = source.find("CtorTag `").expect("tag") as u32;
  let end = start + "CtorTag".len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

/// Construct-only interface + unassigned `var` tag — tsc TS2349 + TS2454 on `tag`
/// (`taggedTemplateWithConstructableTag02`).
#[test]
fn constructable_interface_tag_unassigned_is_not_callable_and_da() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    strict_null_checks: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = "interface I {\n  new (...args: any[]): string;\n}\nvar tag: I;\ntag `Hello`;\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let tag_start = source.rfind("tag `").expect("tag use") as u32;
  let tag_end = tag_start + 3;
  let range = TextRange::new(tag_start, tag_end);

  let not_callable: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::NO_OVERLOAD.as_str()
        && d.primary.file == file_id
        && d.primary.range == range
    })
    .collect();
  assert_eq!(
    not_callable.len(),
    1,
    "expected TC2000 on tag, got {diagnostics:?}"
  );

  let da: Vec<_> = diagnostics
    .iter()
    .filter(|d| {
      d.code.as_str() == codes::USE_BEFORE_ASSIGNMENT.as_str()
        && d.primary.file == file_id
        && d.primary.range == range
    })
    .collect();
  assert_eq!(da.len(), 1, "expected TS2454 on tag, got {diagnostics:?}");
}

/// Valid tagged template packs `TemplateStringsArray` + substitutions (TS2345 on bad subst).
#[test]
fn tagged_template_packs_template_strings_array_args() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = concat!(
    "declare function tag(strs: TemplateStringsArray, n: number): string;\n",
    "tag `${1}`;\n",
    "tag `${\"x\"}`;\n",
  );
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str())
    .collect();
  assert_eq!(
    mismatches.len(),
    1,
    "expected one TS2345 for string subst, got {diagnostics:?}"
  );
  let bad = source.find("\"x\"").expect("bad subst") as u32;
  assert_eq!(mismatches[0].primary.file, file_id);
  assert_eq!(
    mismatches[0].primary.range,
    TextRange::new(bad, bad + 3),
    "TS2345 should sit on the substitution expression"
  );
}

/// someGenerics9-style: first subst fixes T to "", then 0 is TS2345; redecl is TS2403.
#[test]
fn tagged_template_shared_type_param_inference() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    strict_null_checks: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = concat!(
    "function someGenerics9<T>(strs: TemplateStringsArray, a: T, b: T, c: T): T {\n",
    "  return null;\n",
    "}\n",
    "var a9a = someGenerics9 `${ '' }${ 0 }${ [] }`;\n",
    "var a9a: {};\n",
  );
  host.insert(file.clone(), Arc::from(source));
  let file_id = {
    let program = Program::new(host, vec![file.clone()]);
    let file_id = program.file_id(&file).expect("file id");
    let diagnostics = program.check();
    eprintln!(
      "diags: {:?}",
      diagnostics
        .iter()
        .map(|d| (d.code.as_str(), d.primary.range, &d.message))
        .collect::<Vec<_>>()
    );
    let codes_list: Vec<_> = diagnostics.iter().map(|d| d.code.as_str()).collect();
    assert!(
      codes_list
        .iter()
        .any(|c| *c == codes::ARGUMENT_TYPE_MISMATCH.as_str()),
      "expected TS2345, got {diagnostics:?}"
    );
    assert!(
      codes_list
        .iter()
        .any(|c| *c == codes::SUBSEQUENT_VARIABLE_DECLARATIONS.as_str()),
      "expected TS2403, got {diagnostics:?}"
    );
    assert!(
      codes_list
        .iter()
        .any(|c| *c == codes::TYPE_MISMATCH.as_str()),
      "expected TS2322 on return null, got {diagnostics:?}"
    );
    let zero = source.find(" 0 ").expect("0") as u32 + 1;
    let ts2345 = diagnostics
      .iter()
      .find(|d| d.code.as_str() == codes::ARGUMENT_TYPE_MISMATCH.as_str())
      .expect("2345");
    assert_eq!(ts2345.primary.file, file_id);
    assert_eq!(ts2345.primary.range, TextRange::new(zero, zero + 1));
    let a9a_redecl = source.rfind("a9a").expect("redecl") as u32;
    let ts2403: Vec<_> = diagnostics
      .iter()
      .filter(|d| d.code.as_str() == codes::SUBSEQUENT_VARIABLE_DECLARATIONS.as_str())
      .collect();
    assert_eq!(ts2403.len(), 1, "expected one TS2403, got {diagnostics:?}");
    assert_eq!(
      ts2403[0].primary.range,
      TextRange::new(a9a_redecl, a9a_redecl + 3)
    );
    file_id
  };
  let _ = file_id;
}
