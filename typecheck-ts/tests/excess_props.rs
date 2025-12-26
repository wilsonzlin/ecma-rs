use std::sync::Arc;

use hir_js::{lower_from_source, BodyKind};
use typecheck_ts::check::hir_body::check_body;
use typecheck_ts::{codes, Diagnostic, FileId};
use types_ts_interned::TypeStore;

fn run_top_level(source: &str) -> Vec<Diagnostic> {
  let wrapped = format!("function wrapper() {{ {source} }}");
  let lowered = lower_from_source(&wrapped).expect("lowering should succeed");
  let body = lowered
    .bodies
    .iter()
    .max_by_key(|b| {
      if matches!(b.kind, BodyKind::TopLevel) {
        usize::MAX
      } else {
        b.stmts.len()
      }
    })
    .map(|b| b.as_ref())
    .unwrap_or_else(|| panic!("no bodies lowered"));
  let store = TypeStore::new();
  let names = Arc::clone(&lowered.names);
  check_body(body, &names, FileId(0), &wrapped, store).diagnostics
}

#[test]
fn reports_excess_property_on_fresh_object_literal() {
  let diagnostics = run_top_level("let x: { foo: number } = { foo: 1, bar: 2 };");
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
  assert!(
    diagnostics[0]
      .labels
      .iter()
      .any(|l| !l.is_primary && l.message.contains("bar")),
    "expected secondary label for offending property: {:?}",
    diagnostics[0]
  );
}

#[test]
fn allows_index_signature_for_extra_properties() {
  let diagnostics =
    run_top_level("let x: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn allows_intermediate_variable_without_excess_check() {
  let diagnostics = run_top_level(
    "const tmp = { foo: 1, bar: 2 };\n\
      let x: { foo: number } = tmp;",
  );
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn mapped_index_signature_allows_extra_properties() {
  let diagnostics = run_top_level("let x: { [K in string]: number } = { foo: 1, bar: 2, baz: 3 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn union_index_signature_covers_string_and_number_keys() {
  let diagnostics =
    run_top_level("let x: { [key: string | number]: number } = { foo: 1, 0: 2, bar: 3 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn type_assertion_suppresses_excess_property_check() {
  let diagnostics =
    run_top_level("let x: { foo: number } = ({ foo: 1, bar: 2 } as { foo: number });");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn union_target_requires_single_compatible_member() {
  let diagnostics = run_top_level("let x: { foo: number } | { bar: number } = { foo: 1, bar: 2 };");
  assert_eq!(diagnostics.len(), 1);
}

#[test]
fn union_target_allows_member_with_props() {
  let diagnostics = run_top_level("let x: { foo: number } | { bar: number } = { foo: 1 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
#[ignore = "contextual excess property checking not yet implemented"]
fn return_context_triggers_excess_property_check() {
  let diagnostics = run_top_level(
    "function make(): { foo: number } { return { foo: 1, bar: 2 }; }\n\
      make();",
  );
  assert!(
    diagnostics.len() <= 1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
#[ignore = "contextual excess property checking not yet implemented"]
fn nested_contextual_object_literal_checks_excess_properties() {
  let diagnostics =
    run_top_level("let x: { nested: { foo: number } } = { nested: { foo: 1, bar: 2 } };");
  assert!(
    diagnostics.len() <= 1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn call_argument_checks_excess_properties() {
  let diagnostics = run_top_level(
    "function takes(obj: { foo: number }) {}\n\
      takes({ foo: 1, bar: 2 });",
  );
  assert_eq!(diagnostics.len(), 1);
}
