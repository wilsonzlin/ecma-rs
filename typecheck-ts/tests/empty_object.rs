use std::sync::Arc;

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn empty_object_type_accepts_primitives_but_rejects_nullish() {
  let mut host = MemoryHost::default();
  // Use a deterministic file name (`file0.ts` -> `FileId(0)`) so we can assert
  // diagnostics against a stable file id.
  let file = FileKey::new("file0.ts");
  let source = r#"
let ok: {} = 1;
let bad_object: object = 1;
let bad_null: {} = null;
"#;
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();

  let mismatches: Vec<_> = diagnostics
    .iter()
    .filter(|diag| diag.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .collect();
  assert_eq!(mismatches.len(), 2, "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id for a.ts");
  let bad_object_offset = u32::try_from(
    source
      .find("object = 1")
      .expect("bad object assignment"),
  )
  .expect("offset fits in u32")
    + "object = ".len() as u32;
  let bad_null_offset = u32::try_from(source.find("= null").expect("bad null assignment"))
    .expect("offset fits in u32")
    + "= ".len() as u32;

  assert!(
    mismatches.iter().any(|diag| {
      diag.primary.file == file_id
        && diag.primary.range.start <= bad_object_offset
        && diag.primary.range.end >= bad_object_offset + 1
    }),
    "expected mismatch span to cover `object = 1`; got {mismatches:?}",
  );
  assert!(
    mismatches.iter().any(|diag| {
      diag.primary.file == file_id
        && diag.primary.range.start <= bad_null_offset
        && diag.primary.range.end >= bad_null_offset + 1
    }),
    "expected mismatch span to cover `null`; got {mismatches:?}",
  );
}
