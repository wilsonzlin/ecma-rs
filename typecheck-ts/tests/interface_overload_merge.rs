//! Same-name *methods* across merged interface declarations form one overload
//! set with the later declaration's signatures taking precedence (tsc
//! `twoMergedInterfacesWithDifferingOverloads.ts`), and merged generic
//! interfaces unify their type parameters positionally (TS2428 requires
//! identical lists — a second free `T` must not leak into overloads).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn check(opts: CompilerOptions, src: &str) -> Vec<String> {
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
fn later_declaration_overloads_win() {
  // decl2's `(x: T): Date` precedes decl1's `(x: T): number`; `foo(true)`
  // returns Date, so assigning it to `number` must fail.
  let src = r#"
interface B<T> {
    foo(x: T): number;
    foo(x: string): string;
}
interface B<T> {
    foo(x: T): Date;
    foo(x: Date): string;
}
declare var b: B<boolean>;
var r: Date = b.foo(true);
var r2: number = b.foo(true);
"#;
  assert_eq!(check(CompilerOptions::default(), src), vec!["TS2322"]);
}

#[test]
fn all_overloads_remain_available() {
  let src = r#"
interface A {
    foo(x: number): number;
    foo(x: string): string;
}
interface A {
    foo(x: Date): Date;
}
declare var a: A;
a.foo(1);
a.foo(new Date());
a.foo("s");
"#;
  assert_eq!(check(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn merged_generic_interface_instantiates_all_declarations() {
  // decl2's type param unifies with decl1's (positional): no free `T` leaks,
  // so `c.foo(1, 2)` resolves against the merged generic overload set.
  let src = r#"
interface C<T, U> {
    foo(x: T, y: U): string;
    foo(x: string, y: string): number;
}
interface C<T, U> {
    foo<W>(x: W, y: W): W;
}
declare var cc: C<boolean, Date>;
var r2: number = cc.foo(1, 2);
"#;
  assert_eq!(check(CompilerOptions::default(), src), Vec::<String>::new());
}
