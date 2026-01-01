use diagnostics::TextRange;
use typecheck_ts::codes;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn reports_implicit_any_for_params_and_destructuring() {
  let source = "function f(x) { return x; }\nconst {a} = something;";
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  let implicit: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str())
    .collect();
  assert_eq!(
    implicit.len(),
    2,
    "expected exactly two implicit-any diagnostics, got {implicit:?} (all={diagnostics:?})",
  );

  let x_start = source.find("f(x)").expect("expected f(x) in source") as u32 + 2;
  let x_span = TextRange::new(x_start, x_start + 1);
  assert!(
    implicit
      .iter()
      .any(|diag| diag.primary.file == file_id && diag.primary.range == x_span),
    "missing implicit-any diagnostic on parameter `x` at {x_span:?}: {implicit:?}",
  );

  let a_start = source.find("{a}").expect("expected {a} in source") as u32 + 1;
  let a_span = TextRange::new(a_start, a_start + 1);
  assert!(
    implicit
      .iter()
      .any(|diag| diag.primary.file == file_id && diag.primary.range == a_span),
    "missing implicit-any diagnostic on binding `a` at {a_span:?}: {implicit:?}",
  );
}

#[test]
fn reports_implicit_any_for_uncontextualized_arrow_params() {
  let source = "const f = (x) => x;";
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_implicit_any: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  let implicit: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::IMPLICIT_ANY.as_str())
    .collect();
  assert_eq!(
    implicit.len(),
    1,
    "expected exactly one implicit-any diagnostic, got {implicit:?} (all={diagnostics:?})",
  );

  let x_start = source
    .find("(x) =>")
    .expect("expected `(x) =>` in source") as u32
    + 1;
  let x_span = TextRange::new(x_start, x_start + 1);
  assert!(
    implicit
      .iter()
      .any(|diag| diag.primary.file == file_id && diag.primary.range == x_span),
    "missing implicit-any diagnostic on arrow parameter `x` at {x_span:?}: {implicit:?}",
  );
}
