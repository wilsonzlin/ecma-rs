use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{FileId, Host, HostError, Program};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileId, Arc<str>>,
}

impl MemoryHost {
  fn insert(&mut self, id: FileId, source: &str) {
    self.files.insert(id, Arc::from(source.to_string()));
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: FileId, _spec: &str) -> Option<FileId> {
    None
  }
}

#[test]
fn interfaces_merge_members() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(0),
    "interface Foo { a: number; }\ninterface Foo { b: string; }\nconst value: Foo = { a: 1, b: \"ok\" };",
  );

  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d) == Some("Foo".to_string()))
    .expect("interface Foo");
  let ty = program.type_of_def(def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("a") && rendered.contains("b"),
    "merged interface should expose all members, got {rendered}"
  );
}

#[test]
fn namespaces_merge_across_declarations() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(1),
    "namespace N { const a = 1; }\nnamespace N { const b = 2; }\nexport { N };",
  );

  let program = Program::new(host, vec![FileId(1)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let exports = program.exports_of(FileId(1));
  let ns = exports.get("N").expect("namespace export");
  let ty = ns.type_id.expect("namespace type");
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("a") && rendered.contains("b"),
    "namespace merge should expose members, got {rendered}"
  );
}

#[test]
fn value_and_namespace_merge_callable_and_members() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(2),
    "function foo() { return 1; }\nnamespace foo { const bar: string = \"ok\"; }\nexport { foo };",
  );

  let program = Program::new(host, vec![FileId(2)]);
  println!("starting check value_and_namespace_merge_callable_and_members");
  let diagnostics = program.check();
  println!("finished check with {len} diagnostics", len = diagnostics.len());
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let def = program
    .definitions_in_file(FileId(2))
    .into_iter()
    .find(|d| {
      program.def_name(*d) == Some("foo".to_string()) && program.body_of_def(*d).is_some()
    })
    .expect("foo definition");
  println!("computing type of def {:?}", def);
  let ty = program.type_of_def(def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("() =>"),
    "callable side should remain after namespace merge: {rendered}"
  );
  assert!(
    rendered.contains("bar"),
    "namespace members should be visible after merge: {rendered}"
  );
}

#[test]
fn merged_interfaces_expose_members_interned() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(3),
    "interface Foo { a: number; }\ninterface Foo { b: string; }",
  );

  let program = Program::new(host, vec![FileId(3)]);
  let _ = program.check();

  let def = program
    .definitions_in_file(FileId(3))
    .into_iter()
    .find(|d| program.def_name(*d) == Some("Foo".to_string()))
    .expect("interface Foo");
  let ty = program.type_of_def_interned(def);
  let props = program.properties_of(ty);
  let keys: Vec<_> = props
    .iter()
    .filter_map(|p| match &p.key {
      typecheck_ts::PropertyKey::String(name) => Some(name.clone()),
      _ => None,
    })
    .collect();
  assert!(
    keys.contains(&"a".to_string()) && keys.contains(&"b".to_string()),
    "merged interface should expose both properties via interned types"
  );
}

#[test]
fn merged_namespaces_expose_members_interned() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(4),
    "namespace N { const a = 1; }\nnamespace N { const b = 2; }",
  );

  let program = Program::new(host, vec![FileId(4)]);
  let _ = program.check();

  let def = program
    .definitions_in_file(FileId(4))
    .into_iter()
    .find(|d| program.def_name(*d) == Some("N".to_string()))
    .expect("namespace N");
  let ty = program.type_of_def_interned(def);
  let props = program.properties_of(ty);
  let keys: Vec<_> = props
    .iter()
    .filter_map(|p| match &p.key {
      typecheck_ts::PropertyKey::String(name) => Some(name.clone()),
      _ => None,
    })
    .collect();
  assert!(
    keys.contains(&"a".to_string()) && keys.contains(&"b".to_string()),
    "merged namespace should expose members across declarations"
  );
}

#[test]
fn value_namespace_merge_keeps_callability_and_members_interned() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(5),
    "function foo(): number { return 1; }\nnamespace foo { const bar = \"ok\"; }",
  );

  let program = Program::new(host, vec![FileId(5)]);
  let _ = program.check();

  let def = program
    .definitions_in_file(FileId(5))
    .into_iter()
    .find(|d| {
      program.def_name(*d) == Some("foo".to_string()) && program.body_of_def(*d).is_some()
    })
    .expect("foo definition");
  let ty = program.type_of_def_interned(def);
  let props = program.properties_of(ty);
  let has_bar = props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "bar",
    _ => false,
  });
  assert!(has_bar, "namespace member should surface on merged value");
  let calls = program.call_signatures(ty);
  assert!(
    !calls.is_empty(),
    "call signatures should remain after value+namespace merge"
  );
}

#[test]
fn namespace_then_value_prefers_callable_def_and_merges_members() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(6),
    "namespace foo { const bar = 1; }\nfunction foo() { return foo.bar; }\nexport { foo };",
  );

  let program = Program::new(host, vec![FileId(6)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let defs = program.definitions_in_file(FileId(6));
  let func_def = defs
    .iter()
    .copied()
    .find(|d| program.body_of_def(*d).is_some())
    .expect("function definition preserved after merge");
  let exported = program
    .exports_of(FileId(6))
    .get("foo")
    .and_then(|e| e.def)
    .expect("exported foo def");
  assert_eq!(
    exported, func_def,
    "export should point at callable side of merged declaration"
  );

  let namespace_def = defs
    .iter()
    .copied()
    .find(|d| *d != func_def)
    .expect("namespace declaration");

  let ty = program.type_of_def_interned(func_def);
  let props = program.properties_of(ty);
  let has_bar = props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "bar",
    _ => false,
  });
  assert!(has_bar, "namespace member should be visible on merged value");
  let calls = program.call_signatures(ty);
  assert!(
    !calls.is_empty(),
    "call signatures should survive namespace merge with preceding declaration"
  );

  let merged_ns_ty = program.type_of_def_interned(namespace_def);
  let ns_calls = program.call_signatures(merged_ns_ty);
  assert!(
    !ns_calls.is_empty(),
    "namespace side should also expose callable merged type"
  );
  let ns_props = program.properties_of(merged_ns_ty);
  let ns_has_bar = ns_props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "bar",
    _ => false,
  });
  assert!(ns_has_bar, "namespace side should include merged members");
}
