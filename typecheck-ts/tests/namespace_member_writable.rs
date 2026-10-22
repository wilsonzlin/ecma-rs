//! Namespace members are writable unless declared `const` (tsc):
//! `foo.v = …` and `foo.f = …` are legal; `foo.c = …` is TS2540. Covers
//! `externalModules/exportAssignmentMergedModule.ts`.

use typecheck_ts::lib_support::{CompilerOptions, ModuleKind};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn check(src: &str) -> Vec<String> {
  let mut opts = CompilerOptions::default();
  opts.module = Some(ModuleKind::CommonJs);
  let mut host = MemoryHost::with_options(opts);
  let f0 = FileKey::new("foo_0.ts");
  let f1 = FileKey::new("foo_1.ts");
  host.insert(f0.clone(), src);
  host.insert(
    f1.clone(),
    "import foo = require(\"./foo_0\");\nfoo.c = 10;\nfoo.v = 20;\nfoo.l = 30;\nfoo.f = 40;\n",
  );
  let program = Program::new(host, vec![f0, f1]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn var_let_function_members_are_writable() {
  let diags = check(
    r#"namespace Foo {
    export const c = 1;
    export var v = 2;
    export let l = 3;
    export function f() { return 1; }
}
export = Foo;
"#,
  );
  // tsc: only the `const` member is TS2540; the function assignment is a
  // type-mismatch, and `var`/`let` are clean.
  assert!(
    diags.iter().any(|c| c == "TS2540"),
    "expected TS2540 on the const member; got {diags:?}"
  );
  assert!(
    diags.iter().any(|c| c == "TS2322"),
    "expected TS2322 on the function member; got {diags:?}"
  );
  assert_eq!(diags.len(), 2, "exactly two diagnostics; got {diags:?}");
}

#[test]
fn merged_namespace_var_member_is_writable() {
  let diags = check(
    r#"namespace Foo {
	export function a(){
		return 5;
	}
	export var b = true;
}
namespace Foo {
	export function c(a: number){
		return a;
	}
	export namespace Test {
		export var answer = 42;
	}
}
export = Foo;
"#,
  );
  // `foo.Test.answer` is a `var`: writable through the merged namespace.
  assert!(
    !diags.iter().any(|c| c == "TS2540"),
    "no TS2540 expected for var members; got {diags:?}"
  );
}
