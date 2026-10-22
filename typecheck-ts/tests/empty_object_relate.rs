//! The `{}` type relates to object types per tsc: assignable when every
//! property is optional (including the `object` keyword — an empty structural
//! object — and index-signature-only targets like `Record<string, T>`), but
//! not to shapes with required properties or call/construct signatures.
//! Conformance `parser/ecmascript5/Statements/parserForStatement9.ts`
//! (`'a' in {}` is legal; `'a' in 42` is TS2322).

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
fn in_operator_accepts_empty_object_literal_rhs() {
  let src = "for (let [x = 'a' in {}] = []; !x; x = !x) console.log(x)\nfor (let {x = 'a' in {}} = {}; !x; x = !x) console.log(x)\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn in_operator_rejects_primitive_rhs() {
  let src = "let b = 'a' in 42;\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "'in' against a primitive must be TS2322: {c:?}"
  );
}

#[test]
fn empty_object_type_assigns_to_optional_and_indexer_shapes() {
  let src = "declare let e: {};\nlet o: object = e;\nlet a: { a?: number } = e;\nlet r: Record<string, number> = e;\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn empty_object_type_rejects_required_props_and_signatures() {
  let src = "declare let e: {};\nlet d: { a: number } = e;\n";
  assert!(
    codes(src).iter().any(|x| x == "TS2741"),
    "required prop must fail with TS2741"
  );
  let src2 = "declare let e: {};\nlet f: { (): void } = e;\n";
  assert!(
    codes(src2).iter().any(|x| x == "TS2322"),
    "call signature must fail with TS2322"
  );
}
