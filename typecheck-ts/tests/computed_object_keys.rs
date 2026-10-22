//! Computed object-literal keys (tsc `checkComputedPropertyName` +
//! `getIndexInfosOfIndexSymbol` / `getObjectLiteralIndexInfo`):
//!
//! - string/number literal keys become *named* properties (late-bound);
//! - non-literal keys assignable to `string`/`number`/`symbol` contribute to a
//!   synthesized index signature (`any` and numeric-enum keys take the numeric
//!   branch, mixed `string | number` unions the string branch);
//! - the string index also unions in all named sibling properties, the number
//!   index numeric-named siblings (tsc `getObjectLiteralIndexInfo`);
//! - a *number* index signature satisfies a *string* target index signature
//!   (tsc `indexSignaturesRelatedTo`).

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
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
fn numeric_computed_keys_satisfy_string_and_number_indexers() {
  // conformance `es6/computedProperties/computedPropertyNamesContextualType5_ES6.ts`.
  let src = r#"
interface I {
    [s: string]: any;
    [s: number]: any;
}

var o: I = {
    [+"foo"]: "",
    [+"bar"]: 0
}
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn literal_computed_keys_become_named_properties() {
  let src = r#"
const x = { ["a"]: 1, [1]: "s", b: true };
let s: number = x.a;
let t: string = x[1];
let u: boolean = x.b;
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn string_computed_key_unions_sibling_properties_into_index() {
  // tsc `getObjectLiteralIndexInfo`: the string index value is the union of
  // the computed contributions *and* all named sibling properties.
  let src = r#"
declare let k: string;
const x = { [k]: 1, a: "s" };
let n: number = x.whatever;
"#;
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "x.whatever is string | number per tsc → TS2322: {c:?}"
  );
}

#[test]
fn number_computed_key_does_not_union_string_siblings() {
  // The number index only unions numeric-named siblings, so a string-named
  // sibling keeps its own type.
  let src = r#"
declare let k: number;
const x = { [k]: 1, a: "s" };
let s: string = x.a;
let n: number = x[123];
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn computed_key_getter_contributes_to_index() {
  let src = r#"
declare let k: string;
const x = { get [k]() { return 1 as const; } };
"#;
  assert_eq!(codes(src), Vec::<String>::new());
}

// NOTE: object-literal *method* return types are not inferred in expression
// position yet (`{ m() { return 1; } }.m` is `() => unknown`, tsc:
// `() => number`) — a pre-existing gap independent of computed keys, so
// method/index contributions are not asserted here.
