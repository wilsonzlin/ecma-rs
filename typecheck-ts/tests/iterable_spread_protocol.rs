//! Spreading / iterating a non-array object type follows the synchronous
//! iterable protocol (`[Symbol.iterator]().next().value`), matching tsc
//! `getIterationTypeOfIterable` (`iteratorSpreadInArray7.ts`).
//!
//! Two coordinated pieces:
//! - unannotated computed-name methods (`[Symbol.iterator]() { return this; }`)
//!   get their inferred return stamped onto the class instance shape —
//!   previously the refine pass only matched `PropKey::String`, so the
//!   symbol-keyed property stayed `() => any`;
//! - `spread_element_type` / `for_of_element_type` walk the protocol, falling
//!   back to the input object as its own iterator when the method's return
//!   type is a stale snapshot (the `return this` pattern).

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
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

const SYMBOL_ITERATOR: &str = r#"
class SymbolIterator {
    next() {
        return { value: Symbol(), done: false };
    }
    [Symbol.iterator]() {
        return this;
    }
}
"#;

#[test]
fn spread_of_iterable_object_feeds_concat_overloads() {
  let src =
    format!("{SYMBOL_ITERATOR}var array: symbol[];\narray.concat([...new SymbolIterator]);\n");
  // tsc reports only TS2454 (unassigned `array`); the spread itself is a
  // `symbol[]` and satisfies the `ConcatArray<symbol>` rest overload.
  assert_eq!(codes(&src), ["TS2454"]);
}

#[test]
fn spread_of_iterable_object_has_precise_element_type() {
  let src = format!("{SYMBOL_ITERATOR}var z: string[] = [...new SymbolIterator];\n");
  assert_eq!(codes(&src), ["TS2322"]);
}

#[test]
fn for_of_over_iterable_object_yields_element_type() {
  let src =
    format!("{SYMBOL_ITERATOR}for (const s of new SymbolIterator) {{ var q: number = s; }}\n");
  assert_eq!(codes(&src), ["TS2322"]);
}

#[test]
fn spread_of_lib_iterables_uses_declared_type_arguments() {
  let src = "var m = new Map<string, number>();\nvar a = [...m];\nvar bad: string[] = a;\nvar s = new Set<number>();\nvar b = [...s];\nvar bad2: string[] = b;\n";
  assert_eq!(codes(src), ["TS2322", "TS2322"]);
}

#[test]
fn spread_of_array_and_string_still_work() {
  let src =
    "var a: number[] = [1, 2];\nvar b: number[] = [...a];\nvar c: string[] = [...\"ab\"];\n";
  assert!(codes(src).is_empty());
}

#[test]
fn spread_of_non_iterable_stays_unknown_not_error() {
  // No protocol and no array shape: the literal element stays `unknown` (we do
  // not emit TS2488-style diagnostics yet), so it must not suddenly error.
  let src = "var o = { x: 1 };\nvar a = [...o];\n";
  assert!(codes(src).is_empty());
}
