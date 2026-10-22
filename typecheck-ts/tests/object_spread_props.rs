//! Object-literal spreads must contribute enumerable own properties to the
//! inferred shape (tsc CopyDataProperties typing). Without this,
//! `{ ...source }` was typed as `{}` and failed assignability (TS2741/TS2739)
//! — see `intersectionIncludingPropFromGlobalAugmentation`.
//!
//! Also: `EmptyObject` / interface types must expose lib `Object` methods
//! (`hasOwnProperty`) under `--noImplicitAny`.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(src: &str) -> Vec<String> {
  diags_with(src, CompilerOptions::default())
}

fn diags_strict(src: &str) -> Vec<String> {
  let mut opts = CompilerOptions::default();
  opts.no_implicit_any = true;
  opts.strict_null_checks = true;
  diags_with(src, opts)
}

fn diags_with(src: &str, opts: CompilerOptions) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let mut out: Vec<_> = Program::new(host, vec![file])
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn spread_interface_assignable_to_intersection_with_optional() {
  // Upstream: intersectionIncludingPropFromGlobalAugmentation.ts
  let src = r#"
interface Test1 { toString: null | 'string'; }
type Test2 = Test1 & { optional?: unknown };
declare const source: Test1;
const target: Test2 = { ...source };
const hasOwn = target.hasOwnProperty;
export {}
"#;
  assert!(
    diags_strict(src).is_empty(),
    "spread of Test1 must satisfy Test2 + Object methods: {:?}",
    diags_strict(src)
  );
}

#[test]
fn empty_object_exposes_has_own_property() {
  let src = "const h = ({}).hasOwnProperty;\n";
  assert!(
    diags_strict(src).is_empty(),
    "{{}} must expose Object.hasOwnProperty: {:?}",
    diags_strict(src)
  );
}

#[test]
fn spread_copies_interface_properties() {
  let src = r#"
interface A { x: number; y: string }
declare const a: A;
const c: A = { ...a };
"#;
  assert!(
    diags(src).is_empty(),
    "spread must copy interface props: {:?}",
    diags(src)
  );
}

#[test]
fn later_explicit_prop_overrides_spread() {
  let src = r#"
interface A { x: number }
declare const a: A;
const b: { x: string } = { ...a, x: "hi" };
"#;
  assert!(
    diags(src).is_empty(),
    "explicit prop after spread must win: {:?}",
    diags(src)
  );
}

#[test]
fn bare_empty_spread_still_missing_required() {
  let src = r#"
interface A { x: number }
const a: A = { ...{} };
"#;
  assert!(
    diags(src).iter().any(|c| c == "TS2741" || c == "TS2322"),
    "empty spread must not invent required props: {:?}",
    diags(src)
  );
}
