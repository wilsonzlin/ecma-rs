//! tsc erases `readonly` for *property* assignability: a readonly source
//! property is assignable to a writable target (readonly only restricts
//! writes, e.g. TS2540 on assignment). Array/tuple readonlyness is separate
//! (`readonly T[]` ↛ `T[]`). Covers the `as const` options-object pattern in
//! `es2018IntlAPIs.ts` (`supportedLocalesOf(locales, { localeMatcher } as
//! const)`).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn readonly_source_prop_assignable_to_writable_target() {
  let src = r#"
interface W { localeMatcher?: "lookup" | "best fit" }
const options = { localeMatcher: 'lookup' } as const;
const w: W = options;
declare const r: { readonly x: string };
const m: { x: string } = r;
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn readonly_target_prop_still_rejects_writes() {
  // Readonlyness still gates *writes* (TS2540), not assignability.
  let src = r#"
interface R { readonly x: string }
declare const r: R;
r.x = "s";
"#;
  assert_eq!(codes(CompilerOptions::default(), src), vec!["TS2540"]);
}

#[test]
fn readonly_array_stays_incompatible_with_mutable() {
  // Array/tuple readonlyness is a type-kind rule, untouched by the property
  // erasure: `readonly number[]` is not assignable to `number[]` (tsc).
  let src = r#"
declare const r: readonly number[];
const m: number[] = r;
"#;
  assert_eq!(codes(CompilerOptions::default(), src), vec!["TS2322"]);
}
