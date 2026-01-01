use std::sync::Arc;
use typecheck_ts::codes;
use typecheck_ts::{Diagnostic, FileKey, MemoryHost, Program};

fn run(source: &str) -> Vec<Diagnostic> {
  let mut host = MemoryHost::default();
  let key = FileKey::new("input.ts");
  host.insert(key.clone(), Arc::from(source.to_string()));
  let program = Program::new(host, vec![key]);
  program.check()
}

#[test]
fn reports_excess_property_on_fresh_object_literal() {
  let diagnostics = run("let x: { foo: number } = { foo: 1, bar: 2 };");
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn allows_index_signature_for_extra_properties() {
  let diagnostics = run("let x: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn allows_intermediate_variable_without_excess_check() {
  let diagnostics = run(
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
fn type_assertion_suppresses_excess_property_check() {
  let diagnostics = run("let x: { foo: number } = ({ foo: 1, bar: 2 } as { foo: number });");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn union_target_requires_single_compatible_member() {
  let diagnostics = run("let x: { foo: number } | { bar: number } = { foo: 1, bar: 2 };");
  assert_eq!(diagnostics.len(), 1);
}

#[test]
fn union_target_allows_member_with_props() {
  let diagnostics = run("let x: { foo: number } | { bar: number } = { foo: 1 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn return_context_triggers_excess_property_check() {
  let diagnostics = run(
    "function make(): { foo: number } { return { foo: 1, bar: 2 }; }\n\
     make();",
  );
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn nested_contextual_object_literal_checks_excess_properties() {
  let diagnostics = run("let x: { nested: { foo: number } } = { nested: { foo: 1, bar: 2 } };");
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn call_argument_checks_excess_properties() {
  let diagnostics = run(
    "function takes(obj: { foo: number }) {}\n\
     takes({ foo: 1, bar: 2 });",
  );
  assert_eq!(diagnostics.len(), 1);
}

#[test]
fn satisfies_checks_excess_properties() {
  let diagnostics = run("const x = ({ foo: 1, bar: 2 } satisfies { foo: number });");
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn contextual_array_literal_element_checks_excess_properties() {
  let diagnostics = run("let xs: { foo: number }[] = [{ foo: 1, bar: 2 }];");
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn contextual_tuple_literal_element_checks_excess_properties() {
  let diagnostics = run("let xs: [{ foo: number }] = [{ foo: 1, bar: 2 }];");
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn call_argument_nested_contextual_object_literal_checks_excess_properties() {
  let diagnostics = run(
    "function takes(obj: { nested: { foo: number } }) {}\n\
     takes({ nested: { foo: 1, bar: 2 } });",
  );
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn call_argument_array_literal_element_checks_excess_properties() {
  let diagnostics = run(
    "function takes(xs: { foo: number }[]) {}\n\
     takes([{ foo: 1, bar: 2 }]);",
  );
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn assignment_to_typed_identifier_checks_excess_properties() {
  let diagnostics = run("let x: { foo: number };\nx = { foo: 1, bar: 2 };");
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}

#[test]
fn assignment_to_typed_member_checks_excess_properties() {
  let diagnostics = run(
    "let obj: { nested: { foo: number } } = { nested: { foo: 1 } };\n\
     obj.nested = { foo: 1, bar: 2 };",
  );
  assert_eq!(
    diagnostics.len(),
    1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "unexpected diagnostic: {:?}",
    diagnostics[0]
  );
}
