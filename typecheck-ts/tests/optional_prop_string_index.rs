use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn optional_props_assignable_to_string_index_not_number_index() {
  let src = r#"
declare let optionalProperties: { k1?: string };
declare let undefinedProperties: { k1: string | undefined };
declare let stringDictionary: { [key: string]: string };
stringDictionary = optionalProperties;
stringDictionary = undefinedProperties;

declare let probablyArray: { [key: number]: string };
declare let numberLiteralKeys: { 1?: string };
probablyArray = numberLiteralKeys;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let starts: Vec<usize> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .map(|d| d.primary.range.start as usize)
    .collect();
  let opt_ok = src.find("stringDictionary = optionalProperties").unwrap();
  let undef_err = src.find("stringDictionary = undefinedProperties").unwrap();
  let num_err = src.find("probablyArray = numberLiteralKeys").unwrap();
  assert!(
    !starts
      .iter()
      .any(|&s| s == opt_ok || (s > opt_ok && s < undef_err)),
    "optionalProperties should be ok, starts={starts:?}"
  );
  assert!(
    starts
      .iter()
      .any(|&s| s == undef_err || (s >= undef_err && s < num_err)),
    "undefinedProperties should error, starts={starts:?}"
  );
  assert!(
    starts.iter().any(|&s| s >= num_err),
    "numberLiteralKeys should error, starts={starts:?}"
  );
}

#[test]
fn sequential_ok_assign_still_checks_declared_index_type() {
  // After a successful assign, the next write must still use the declared
  // index signature — not the narrowed RHS object type.
  let src = r#"
declare let optionalProperties: { k1?: string };
declare let undefinedProperties: { k1: string | undefined };
declare let stringDictionary: { [key: string]: string };
stringDictionary = optionalProperties;
stringDictionary = undefinedProperties;
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert_eq!(ts2322.len(), 1, "expected one TS2322, got {diags:?}");
  let undef = src.find("stringDictionary = undefinedProperties").unwrap() as u32;
  assert_eq!(ts2322[0].primary.range.start, undef);
}

#[test]
fn generic_optional_prop_assignable_to_string_index_with_union() {
  // Oracle: optionalPropertyAssignableToStringIndexSignature.ts `f<T>()`.
  let src = r#"
function f<T>() {
  let optional: { k1?: T } = undefined!;
  let dict: { [key: string]: T | number } = optional;
}
"#;
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let ts2322: Vec<_> = diags
    .iter()
    .filter(|d| d.code.as_str() == "TS2322")
    .collect();
  assert!(
    ts2322.is_empty(),
    "undefined! and optional→string index should be ok, got {diags:?}"
  );
}
