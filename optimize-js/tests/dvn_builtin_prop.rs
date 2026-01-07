#![cfg(feature = "serde")]

#[path = "common/mod.rs"]
mod common;
use common::compile_source;
use optimize_js::TopLevelMode;
use serde_json::Value;

fn debug_step(source: &str, name: &str) -> Value {
  let program = compile_source(source, TopLevelMode::Module, true);
  let debug = program
    .top_level
    .debug
    .expect("debug output should be available when enabled");
  let debug_json = serde_json::to_value(&debug).expect("serialize debug output");
  let steps = debug_json
    .get("steps")
    .and_then(|steps| steps.as_array())
    .expect("steps array");
  steps
    .iter()
    .find(|step| step.get("name").and_then(|name| name.as_str()) == Some(name))
    .cloned()
    .unwrap_or_else(|| panic!("missing debug step {name}"))
}

fn builtin_values(step: &Value) -> Vec<String> {
  fn collect(value: &Value, out: &mut Vec<String>) {
    match value {
      Value::Object(map) => {
        if let Some(v) = map.get("Builtin").and_then(|v| v.as_str()) {
          out.push(v.to_string());
        }
        for v in map.values() {
          collect(v, out);
        }
      }
      Value::Array(items) => items.iter().for_each(|v| collect(v, out)),
      _ => {}
    }
  }

  let mut out = Vec::new();
  collect(step, &mut out);
  out
}

#[test]
fn folds_builtin_member_when_identifier() {
  let step = debug_step("const x = Math.round(1.2);", "opt1_dvn");
  let builtins = builtin_values(&step);
  assert!(
    builtins.contains(&"Math.round".to_string()),
    "expected folded builtin path; builtins seen: {builtins:?}"
  );
}

#[test]
fn does_not_fold_non_identifier_property() {
  let step = debug_step("const x = Math['not-valid-ident'](1);", "opt1_dvn");
  let builtins = builtin_values(&step);
  assert!(
    !builtins.contains(&"Math.not-valid-ident".to_string()),
    "invalid identifier property should not be folded; builtins seen: {builtins:?}"
  );
  assert!(
    step.to_string().contains("not-valid-ident"),
    "debug step should still reference the original property name"
  );
}
