//! Reading a setter-only private accessor is TS2806 ("Private accessor was
//! defined without a getter"), never TS2339 — the accessor exists for
//! visibility purposes, so the private-access existence check must not also
//! fire (`privateNameSetterNoGetter.ts`). Covers plain reads and compound
//! assignments (which read the LHS).

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

#[test]
fn compound_assignment_reads_setter_only_private() {
  let src = "const C = class {\n    set #x(x) {}\n    m() {\n        this.#x += 2;\n    }\n}";
  assert_eq!(codes(src), ["TS2806"]);
}

#[test]
fn plain_read_of_setter_only_private() {
  let src = "const C = class {\n    set #x(x) {}\n    m() {\n        return this.#x;\n    }\n}";
  assert_eq!(codes(src), ["TS2806"]);
}

#[test]
fn getter_setter_pair_reads_cleanly() {
  let src = "class C {\n    get #x() { return 1; }\n    set #x(x) {}\n    m() {\n        this.#x += 2;\n        return this.#x;\n    }\n}";
  assert!(codes(src).is_empty());
}
