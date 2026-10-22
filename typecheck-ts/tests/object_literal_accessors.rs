//! Object-literal getter/setter pairs fold into a semantic property type:
//! the property's type is the getter's return (or the setter's parameter
//! when setter-only), writable when a setter exists. Reads and writes never
//! see the raw overloaded `(): R & (p: P) => void` callable that same-key
//! interning would produce
//! (`emitCompoundExponentiationAssignmentWithIndexingOnLHS3`).

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

const PAIR: &str = "var object = {\n    _0: 2,\n    get 0() {\n        return this._0;\n    },\n    set 0(x: number) {\n        this._0 = x;\n    },\n}\n";

#[test]
fn numeric_accessor_compound_chains_are_clean() {
  let src = format!("{PAIR}object[0] **= object[0];\nobject[0] **= object[0] **= 2;\nobject[0] **= object[0] ** 2;\n");
  assert!(codes(&src).is_empty());
}

#[test]
fn numeric_accessor_plain_read_and_write_are_clean() {
  let src = format!("{PAIR}var n: number = object[0];\nobject[0] = object[0] + 1;\n");
  assert!(codes(&src).is_empty());
}

#[test]
fn string_accessor_read_is_clean() {
  let src = "var o = {\n    _0: 2,\n    get x() {\n        return this._0;\n    },\n    set x(v: number) {\n        this._0 = v;\n    },\n}\nvar n: number = o['x'];\nvar m: number = o.x;\n";
  assert!(codes(src).is_empty());
}

#[test]
fn getter_only_pair_still_types_reads() {
  let src = "var o = { get y() { return 1; } };\nvar k: number = o.y;\n";
  assert!(codes(src).is_empty());
}
