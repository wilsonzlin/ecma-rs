//! For-of heads bind the loop variable (TDZ) before the iterable is
//! evaluated: `for await (await using of of of)` resolves `of` and reports
//! TS2448 (TDZ) — not TS2304 (`awaitUsingDeclarationsInForAwaitOf.2.ts`,
//! tsc issue #55555).

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
fn await_using_of_is_tdz_not_unresolved() {
  let src = "async function test() {\n  for await (await using of of of) {};\n}\n";
  let c = codes(src);
  assert_eq!(c, vec!["TS2448".to_string()], "only TS2448 (tsc): {c:?}");
}

#[test]
fn let_x_of_x_is_tdz_not_unresolved() {
  // tsc: TS2448 (+ TS7022, which we do not implement); never TS2304.
  let src = "for (let x of x) {}\n";
  let c = codes(src);
  assert_eq!(c, vec!["TS2448".to_string()], "only TS2448: {c:?}");
}

#[test]
fn normal_for_of_still_works() {
  let src = "for (const x of [1, 2]) {\n  let n: number = x;\n}\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn for_of_element_type_still_flows() {
  // The element type must still flow from the (now seeded) RHS.
  let src = "for (const x of [1, 2]) {\n  let s: string = x;\n}\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "element type must still flow (number ↛ string): {c:?}"
  );
}
