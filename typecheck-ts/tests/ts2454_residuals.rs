//! TS2454 residuals vs tsc 5.9.3 (`--strict`):
//! - type-alias annotations that resolve to DA-exempt types
//! - generic / imported type-alias DA expansion (args, defaults, re-exports)
//! - `for (let v of v)` → TS2448 (not TS2454)
//! - `x!` non-null assertion suppresses TS2454
//! - `(x)!` does *not* suppress TS2454 (paren breaks NonNull parent; `(x!)` does)
//! - destructuring sibling defaults (`{ a, b = a }`, `[a, b = a]`, rest+sibling)
//! - ambient `declare let` is assumed initialized (no spurious TS2454)

use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(src: &str) -> Vec<(String, String)> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| matches!(d.code.as_str(), "TS2454" | "TS2448"))
    .map(|d| (d.code.as_str().to_string(), d.message.clone()))
    .collect();
  out.sort();
  out
}

fn codes_only(src: &str) -> Vec<String> {
  diags(src).into_iter().map(|(c, _)| c).collect()
}

#[test]
fn type_alias_any_is_da_exempt() {
  let src = r#"
type A = any;
function f() {
  let x: A;
  return x;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "tsc exempts alias→any: {:?}",
    diags(src)
  );
}

#[test]
fn type_alias_string_or_undefined_is_da_exempt() {
  let src = r#"
type U = string | undefined;
function f() {
  let y: U;
  return y;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "tsc exempts alias→T|undefined: {:?}",
    diags(src)
  );
}

#[test]
fn type_alias_number_still_reports_ts2454() {
  let src = r#"
type N = number;
function f() {
  let x: N;
  return x;
}
"#;
  let codes = codes_only(src);
  assert_eq!(
    codes,
    vec!["TS2454".to_string()],
    "non-exempt alias must still DA-check: {:?}",
    diags(src)
  );
}

#[test]
fn for_of_shadowing_rhs_is_ts2448_not_ts2454() {
  // Upstream es6/for-ofStatements/for-of55.ts
  let src = r#"
let v = [1];
for (let v of v) {
  v;
}
"#;
  let codes = codes_only(src);
  assert!(
    codes.iter().any(|c| c == "TS2448"),
    "expected TS2448 for for-of55: {:?}",
    diags(src)
  );
  assert!(
    !codes.iter().any(|c| c == "TS2454"),
    "for-of55 must not also emit TS2454: {:?}",
    diags(src)
  );
}

#[test]
fn let_self_init_reports_ts2448() {
  let src = r#"
function f() {
  let a: number = a;
  return a;
}
"#;
  let codes = codes_only(src);
  assert!(
    codes.iter().any(|c| c == "TS2448"),
    "expected TS2448 on let a = a: {:?}",
    diags(src)
  );
}

#[test]
fn nonnull_assertion_suppresses_ts2454() {
  let src = r#"
function f() {
  let x: number;
  return x!;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "tsc assumeInitialized under NonNullExpression: {:?}",
    diags(src)
  );
}

#[test]
fn parenthesized_nonnull_operand_still_reports_ts2454() {
  // tsc: `node.parent.kind === NonNullExpression` — `(x)!` has Parenthesized
  // parent, so DA is not suppressed (unlike bare `x!`).
  let src = r#"
function f() {
  let x: number;
  return (x)!;
}
"#;
  assert_eq!(
    codes_only(src),
    vec!["TS2454".to_string()],
    "(x)! must still DA-check: {:?}",
    diags(src)
  );
}

#[test]
fn parenthesized_nonnull_expression_suppresses_ts2454() {
  // `(x!)` — identifier's parent is still NonNullExpression.
  let src = r#"
function f() {
  let x: number;
  return (x!);
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "(x!) still assumeInitialized: {:?}",
    diags(src)
  );
}

#[test]
fn bare_unassigned_still_reports_ts2454() {
  let src = r#"
function g() {
  let x: number;
  return x;
}
"#;
  assert_eq!(
    codes_only(src),
    vec!["TS2454".to_string()],
    "control: bare use still TS2454: {:?}",
    diags(src)
  );
}

#[test]
fn definite_assignment_assertion_still_exempt() {
  let src = r#"
function f() {
  let x!: number;
  return x;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "let x!: T already assigned: {:?}",
    diags(src)
  );
}

#[test]
fn object_destructuring_sibling_default_no_ts2454() {
  // Upstream es6/destructuring/destructuringObjectBindingPatternAndAssignment9SiblingInitializer.ts
  let src = r#"
function f() {
  const { a1, b1 = a1 } = { a1: 1 };
  const { a2, b2 = 1 + a2 } = { a2: 1 };
  return b1 + b2;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "prior object siblings are assigned before later defaults: {:?}",
    diags(src)
  );
}

#[test]
fn array_destructuring_sibling_default_no_ts2454() {
  // Upstream es6/destructuring/destructuringArrayBindingPatternAndAssignment5SiblingInitializer.ts
  let src = r#"
function f() {
  const [a1, b1 = a1] = [1];
  const [a2, b2 = 1 + a2] = [1];
  return b1 + b2;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "prior array siblings are assigned before later defaults: {:?}",
    diags(src)
  );
}

#[test]
fn rest_then_sibling_default_no_ts2454() {
  // Upstream es6/destructuring/destructuringEvaluationOrder.ts (#39181)
  let src = r#"
function f() {
  let [{ ...a }, b = a]: any[] = [{ x: 1 }];
  return b;
}
"#;
  assert!(
    !codes_only(src).iter().any(|c| c == "TS2454"),
    "rest binding a is assigned before b = a: {:?}",
    diags(src)
  );
}

#[test]
fn self_referential_destructuring_default_still_ts2454() {
  let src = r#"
function f() {
  const { a: x = x } = { a: 1 };
  return x;
}
"#;
  assert!(
    codes_only(src)
      .iter()
      .any(|c| c == "TS2454" || c == "TS2448"),
    "self-ref default must remain an error: {:?}",
    diags(src)
  );
}

#[test]
fn bare_let_still_reports_ts2454_after_sibling_fix() {
  let src = r#"
function f() {
  let x: number;
  return x;
}
"#;
  assert_eq!(
    codes_only(src),
    vec!["TS2454".to_string()],
    "leaf Assigned during bind must not leak past no-init declarators: {:?}",
    diags(src)
  );
}

#[test]
fn ambient_declare_let_no_ts2454() {
  let src = r#"
// @strict: true
declare let x: { a: 0 | 1 | undefined };
let { a: a1 } = x;
let b1 = x.a;
"#;
  assert!(
    !codes_only(src).iter().any(|c| c == "TS2454"),
    "declare let is ambient-initialized: {:?}",
    diags(src)
  );
}

#[test]
fn ambient_declare_let_logical_assign_no_ts2454() {
  let src = r#"
declare let x: { a?: boolean };
x.a ??= true;
x.a &&= false;
"#;
  assert!(
    !codes_only(src).iter().any(|c| c == "TS2454"),
    "declare let logical assign: {:?}",
    diags(src)
  );
}

#[test]
fn generic_alias_subst_da_exemptions() {
  // tsc: Box<string>, Id<any>, Id (default any), Just<string|undefined> exempt;
  // Id<number> / Id2 (default number) report TS2454.
  let src = r#"
type Box<T> = T | undefined;
type Id<T> = T;
type IdDefault<T = any> = T;
type IdNumDefault<T = number> = T;
type Just<T> = T;
type V<T> = Id<T>;
function f() {
  let a: Box<string>;
  let b: Id<any>;
  let c: IdDefault;
  let d: Id<number>;
  let e: IdNumDefault;
  let g: Just<string | undefined>;
  let h: V<any>;
  return [a, b, c, d, e, g, h];
}
"#;
  let codes = codes_only(src);
  let ts2454 = codes.iter().filter(|c| *c == "TS2454").count();
  assert_eq!(
    ts2454,
    2,
    "expected TS2454 only on Id<number> and IdNumDefault: {:?}",
    diags(src)
  );
}

#[test]
fn imported_alias_da_exemptions() {
  let mut host = MemoryHost::new();
  let a = FileKey::new("a.ts");
  let b = FileKey::new("b.ts");
  let entry = FileKey::new("entry.ts");
  host.insert(
    a.clone(),
    "export type A = any;\nexport type N = number;\nexport type Box<T> = T | undefined;\n",
  );
  host.insert(b.clone(), "export type { A as AnyAlias } from \"./a\";\n");
  host.insert(
    entry.clone(),
    r#"
import type { A, N, Box } from "./a";
import type { AnyAlias } from "./b";
function f() {
  let a: A;
  let n: N;
  let box: Box<string>;
  let r: AnyAlias;
  return [a, n, box, r];
}
"#,
  );
  host.link(entry.clone(), "./a", a.clone());
  host.link(entry.clone(), "./b", b.clone());
  host.link(b, "./a", a);
  let program = Program::new(host, vec![entry]);
  let mut msgs: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == "TS2454")
    .map(|d| d.message.clone())
    .collect();
  msgs.sort();
  assert_eq!(
    msgs,
    vec!["n is used before being assigned".to_string()],
    "only non-exempt imported N should DA-check: {msgs:?}"
  );
}

#[test]
fn bare_true_conditional_suppresses_da_on_false_branch() {
  // tsc binder: TrueKeyword → FalseCondition is UnreachableFlow (no TS2454).
  let src = r#"
function f() {
  let a: number;
  let b: number;
  return true ? a : b;
}
"#;
  let msgs: Vec<_> = diags(src).into_iter().map(|(_, m)| m).collect();
  assert_eq!(
    msgs,
    vec!["a is used before being assigned".to_string()],
    "only true-branch should DA-check: {:?}",
    diags(src)
  );
}

#[test]
fn bare_false_conditional_suppresses_da_on_true_branch() {
  let src = r#"
function f() {
  let a: number;
  let b: number;
  return false ? a : b;
}
"#;
  let msgs: Vec<_> = diags(src).into_iter().map(|(_, m)| m).collect();
  assert_eq!(
    msgs,
    vec!["b is used before being assigned".to_string()],
    "only false-branch should DA-check: {:?}",
    diags(src)
  );
}

#[test]
fn parenthesized_true_conditional_still_da_checks_both_branches() {
  // `(true)` is ParenthesizedExpression — not bare TrueKeyword.
  let src = r#"
function f() {
  let a: number;
  let b: number;
  return (true) ? a : b;
}
"#;
  let mut msgs: Vec<_> = diags(src).into_iter().map(|(_, m)| m).collect();
  msgs.sort();
  assert_eq!(
    msgs,
    vec![
      "a is used before being assigned".to_string(),
      "b is used before being assigned".to_string(),
    ],
    "(true) must DA-check both branches: {:?}",
    diags(src)
  );
}

#[test]
fn bare_false_logical_and_suppresses_da_on_rhs() {
  let src = r#"
function f() {
  let a: number;
  return false && a;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "false && rhs is unreachable for TS2454: {:?}",
    diags(src)
  );
}

#[test]
fn bare_true_logical_or_suppresses_da_on_rhs() {
  let src = r#"
function f() {
  let a: number;
  return true || a;
}
"#;
  assert!(
    codes_only(src).is_empty(),
    "true || rhs is unreachable for TS2454: {:?}",
    diags(src)
  );
}

#[test]
fn bare_true_if_suppresses_da_on_else() {
  let src = r#"
function f() {
  let a: number;
  let b: number;
  if (true) {
    a;
  } else {
    b;
  }
}
"#;
  let msgs: Vec<_> = diags(src).into_iter().map(|(_, m)| m).collect();
  assert_eq!(
    msgs,
    vec!["a is used before being assigned".to_string()],
    "if (true) else is unreachable for TS2454: {:?}",
    diags(src)
  );
}
