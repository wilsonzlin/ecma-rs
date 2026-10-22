//! A super call expression has type `void` (tsc `superCalls.ts`):
//! `var p = super(''); var p = v();` does not fire TS2403 when both
//! declarations are `void`. Argument expressions are still checked for their
//! own diagnostics.

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
fn super_call_expression_is_void() {
  let src = r#"
class Base {
    x = 43;
    constructor(n: string) {
    }
}

function v(): void { }

class Derived extends Base {
    constructor(public q: number) {
        super('');
        var p = super('');
        var p = v();
    }
}

class OtherBase {
}

class OtherDerived extends OtherBase {
    constructor() {
        var p = '';
        super();
    }
}
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn super_call_arguments_still_checked() {
  // `super(y)` with an undeclared `y` still reports TS2304 (the void result
  // must not short-circuit argument-expression checking).
  let src = r#"
class Base {
    constructor(n: number) {
    }
}
class Derived extends Base {
    constructor() {
        super(y);
    }
}
"#;
  let diags = codes(CompilerOptions::default(), src);
  assert_eq!(diags, vec!["TS2304"]);
}
