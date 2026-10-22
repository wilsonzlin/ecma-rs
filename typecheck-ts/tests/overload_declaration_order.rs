//! Overloaded method calls resolve the first *applicable* overload in
//! declaration order (tsc `typesWithSpecializedCallSignatures.ts`): duplicate
//! same-name method props merge by concatenating overload lists (not via the
//! intersection canonicalizer's `TypeId` sort, which scrambles declaration
//! order).

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

const OVERLOADS: &str = r#"
class Base { foo: string }
class Derived1 extends Base { bar: string }
class Derived2 extends Base { baz: string }

class C {
    foo(x: 'hi'): Derived1;
    foo(x: 'bye'): Derived2;
    foo(x: string): Base;
    foo(x) {
        return x;
    }
}
var c = new C();
var r1: Derived1 = c.foo('hi');
var r2: Derived2 = c.foo('bye');
var r3: Base = c.foo('hm');
"#;

#[test]
fn first_applicable_overload_in_declaration_order_wins() {
  // The specialized `'hi'`/`'bye'` overloads lead the set; the general
  // `string` overload trails. Any order scrambling makes `r1` fail with
  // TS2741 (`Base` lacks `bar`).
  assert_eq!(
    codes(CompilerOptions::default(), OVERLOADS),
    Vec::<String>::new()
  );
}

#[test]
fn interface_overload_order_preserved_through_assignment() {
  // Same specialized set, but reached through interface/object-literal types
  // (interface prop merging path).
  let src = r#"
class Base { foo: string }
class Derived1 extends Base { bar: string }
class Derived2 extends Base { baz: string }

interface I {
    foo(x: 'hi'): Derived1;
    foo(x: 'bye'): Derived2;
    foo(x: string): Base;
}
declare var i: I;
var r1: Derived1 = i.foo('hi');
var r2: Derived2 = i.foo('bye');
var r3: Base = i.foo('hm');
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}
