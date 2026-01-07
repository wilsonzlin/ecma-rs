use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{FileKey, Host, HostError, Program};
use types_ts_interned::TypeKind as InternedTypeKind;

fn fk(id: u32) -> FileKey {
  FileKey::new(format!("file{id}.ts"))
}

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
}

impl MemoryHost {
  fn insert(&mut self, key: FileKey, source: &str) {
    self.files.insert(key, Arc::from(source.to_string()));
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: &FileKey, _spec: &str) -> Option<FileKey> {
    None
  }
}

#[test]
fn interfaces_merge_members() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("merge.ts");
  host.insert(
    key.clone(),
    "interface Foo { a: number; }\ninterface Foo { b: string; }\nconst value: Foo = { a: 1, b: \"ok\" };",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
  let def = program
    .definitions_in_file(program.file_id(&key).expect("file id"))
    .into_iter()
    .find(|d| program.def_name(*d) == Some("Foo".to_string()))
    .expect("interface Foo");
  let ty = program.type_of_def(def);
  let props = program.properties_of(ty);
  let has_a = props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "a",
    _ => false,
  });
  let has_b = props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "b",
    _ => false,
  });
  assert!(has_a && has_b, "merged interface should expose all members");
  let a_ty = program
    .property_type(ty, typecheck_ts::PropertyKey::String("a".to_string()))
    .expect("merged property a");
  assert_eq!(program.display_type(a_ty).to_string(), "number");
  let b_ty = program
    .property_type(ty, typecheck_ts::PropertyKey::String("b".to_string()))
    .expect("merged property b");
  assert_eq!(program.display_type(b_ty).to_string(), "string");
}

#[test]
fn namespaces_merge_across_declarations() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("ns.ts");
  host.insert(
    key.clone(),
    "namespace N { export const a = 1; }\nnamespace N { export const b = 2; }\nexport { N };",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
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
  let key = fk(2);
  host.insert(
    key.clone(),
    "function foo() { return 1; }\nnamespace foo { export const bar: string = \"ok\"; }\nexport { foo };",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d) == Some("foo".to_string()) && program.body_of_def(*d).is_some())
    .expect("foo definition");
  let ty = program.type_of_def(def);
  let call_sigs = program.call_signatures(ty);
  assert!(
    !call_sigs.is_empty(),
    "callable side should remain after namespace merge: {}",
    program.display_type(ty)
  );
  let bar_ty = program
    .property_type(ty, typecheck_ts::PropertyKey::String("bar".to_string()))
    .expect("namespace member 'bar' should be visible after merge");
  assert_eq!(program.display_type(bar_ty).to_string(), "string");
}

#[test]
fn merged_interfaces_expose_members_interned() {
  let mut host = MemoryHost::default();
  let key = fk(3);
  host.insert(
    key.clone(),
    "interface Foo { a: number; }\ninterface Foo { b: string; }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
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
  let key = fk(4);
  host.insert(
    key.clone(),
    "namespace N { export const a = 1; }\nnamespace N { export const b = 2; }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
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
fn namespace_value_members_use_member_types() {
  let mut host = MemoryHost::default();
  let key = fk(7);
  let source = "namespace N { export const x: string = \"hi\"; }\nconst y = N.x;\ny;";
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let x_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d) == Some("x".to_string()))
    .expect("namespace member def");
  let x_def_kind = program.interned_type_kind(program.type_of_def_interned(x_def));
  assert!(
    matches!(x_def_kind, InternedTypeKind::String),
    "member def should honor annotation, got {x_def_kind:?}"
  );
  let ns_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d) == Some("N".to_string()))
    .expect("namespace definition");
  let ns_ty = program.type_of_def_interned(ns_def);
  let props = program.properties_of(ns_ty);
  if std::env::var("TRACE_NS").is_ok() {
    eprintln!(
      "namespace props: {:?}",
      props
        .iter()
        .map(|p| {
          (
            match &p.key {
              typecheck_ts::PropertyKey::String(name) => name.clone(),
              _ => String::new(),
            },
            program.interned_type_kind(p.ty),
          )
        })
        .collect::<Vec<_>>()
    );
    let defs: Vec<_> = program
      .definitions_in_file(file_id)
      .into_iter()
      .map(|d| (d, program.def_name(d)))
      .collect();
    eprintln!("defs: {:?}", defs);
  }
  let x_prop = props.iter().find(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "x",
    _ => false,
  });
  let x_prop = x_prop.expect("namespace member x");
  let x_kind = program.interned_type_kind(x_prop.ty);
  assert!(
    matches!(x_kind, InternedTypeKind::String),
    "namespace member type should respect declared annotation, got {x_kind:?}"
  );
  let offset_x = source
    .find("N.x")
    .map(|idx| idx as u32 + 2)
    .expect("offset for N.x");
  let ty = program.type_at(file_id, offset_x).expect("type at N.x");
  assert_eq!(
    program.display_type(ty).to_string(),
    "string",
    "namespace property should retain declared type"
  );
  let offset_y = source
    .rfind("y;")
    .map(|idx| idx as u32)
    .expect("offset for y usage");
  let y_ty = program.type_at(file_id, offset_y).expect("type at y");
  assert_eq!(
    program.display_type(y_ty).to_string(),
    "string",
    "namespace member access should flow through to value users"
  );
}

#[test]
fn namespace_omits_type_only_members() {
  let mut host = MemoryHost::default();
  let key = fk(8);
  host.insert(key.clone(), "namespace N { export interface I {} }");

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d) == Some("N".to_string()))
    .expect("namespace N");
  let ty = program.type_of_def_interned(def);
  let props = program.properties_of(ty);
  let has_interface = props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "I",
    _ => false,
  });
  assert!(
    !has_interface,
    "type-only members should not surface on namespace values"
  );
  let missing_prop = program.property_type(
    program.type_of_def(def),
    typecheck_ts::PropertyKey::String("I".to_string()),
  );
  if let Some(prop_ty) = missing_prop {
    assert_eq!(
      program.display_type(prop_ty).to_string(),
      "unknown",
      "type-only namespace members should not have meaningful value types"
    );
  }
}

#[test]
fn value_namespace_merge_keeps_callability_and_members_interned() {
  let mut host = MemoryHost::default();
  let key = fk(5);
  host.insert(
    key.clone(),
    "function foo(): number { return 1; }\nnamespace foo { export const bar = \"ok\"; }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d) == Some("foo".to_string()) && program.body_of_def(*d).is_some())
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
  let key = fk(6);
  host.insert(
    key.clone(),
    "function foo() { return foo.bar; }\nnamespace foo { export const bar = 1; }\nexport { foo };",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let defs = program.definitions_in_file(file_id);
  let mut foo_defs: Vec<_> = defs
    .iter()
    .copied()
    .filter(|d| program.def_name(*d) == Some("foo".to_string()))
    .collect();
  foo_defs.sort_by_key(|d| {
    program
      .def_span(*d)
      .map(|span| span.range.start)
      .unwrap_or(u32::MAX)
  });
  assert_eq!(
    foo_defs.len(),
    2,
    "expected two merged defs for foo, got {foo_defs:?}"
  );
  let func_def = foo_defs[0];
  let namespace_def = foo_defs[1];
  let exported = program
    .exports_of(file_id)
    .get("foo")
    .and_then(|e| e.def)
    .expect("exported foo def");
  assert_eq!(
    exported, func_def,
    "export should point at callable side of merged declaration"
  );

  let ty = program.type_of_def_interned(func_def);
  let props = program.properties_of(ty);
  let has_bar = props.iter().any(|p| match &p.key {
    typecheck_ts::PropertyKey::String(name) => name == "bar",
    _ => false,
  });
  assert!(
    has_bar,
    "namespace member should be visible on merged value"
  );
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
