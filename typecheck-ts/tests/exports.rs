use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts::{codes, FileKey, Host, HostError, Program, TextRange};

fn fk(id: u32) -> FileKey {
  FileKey::new(format!("file{id}.ts"))
}

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
  edges: HashMap<(FileKey, String), FileKey>,
}

impl MemoryHost {
  fn insert(&mut self, key: FileKey, source: &str) {
    self.files.insert(key, Arc::from(source.to_string()));
  }

  fn link(&mut self, from: FileKey, specifier: &str, to: FileKey) {
    self.edges.insert((from, specifier.to_string()), to);
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

  fn resolve(&self, from: &FileKey, spec: &str) -> Option<FileKey> {
    self.edges.get(&(from.clone(), spec.to_string())).cloned()
  }
}

#[test]
fn value_exports_follow_reexport_chain() {
  let mut host = MemoryHost::default();
  let key_a = fk(0);
  let key_b = fk(1);
  let key_c = fk(2);
  host.insert(key_a.clone(), "export const foo: number = 1;");
  host.insert(key_b.clone(), "export { foo as bar } from \"./a\";");
  host.insert(key_c.clone(), "export * from \"./b\";");
  host.link(key_b.clone(), "./a", key_a.clone());
  host.link(key_c.clone(), "./b", key_b.clone());

  let program = Program::new(host, vec![key_c.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_a = program.file_id(&key_a).expect("file a");
  let file_b = program.file_id(&key_b).expect("file b");
  let file_c = program.file_id(&key_c).expect("file c");

  let exports_b = program.exports_of(file_b);
  let bar_entry_b = exports_b.get("bar").expect("bar export in module b");
  assert!(bar_entry_b.def.is_none());
  let bar_type_b = bar_entry_b.type_id.expect("type for bar in module b");
  assert_eq!(program.display_type(bar_type_b).to_string(), "number");

  let exports_c = program.exports_of(file_c);
  let bar_entry_c = exports_c.get("bar").expect("bar export in module c");
  assert!(bar_entry_c.def.is_none());
  let bar_type_c = bar_entry_c.type_id.expect("type for bar in module c");
  assert_eq!(program.display_type(bar_type_c).to_string(), "number");

  let exports_a = program.exports_of(file_a);
  let foo_entry = exports_a.get("foo").expect("foo export in module a");
  assert!(foo_entry.def.is_some());
  let foo_type = foo_entry.type_id.expect("type for foo");
  assert_eq!(program.display_type(foo_type).to_string(), "number");
}

#[test]
fn string_literal_exports_follow_reexport_chain_and_export_star() {
  let mut host = MemoryHost::default();
  let key_dep = fk(410);
  let key_mid = fk(411);
  let key_root = fk(412);
  let key_entry = fk(413);
  host.insert(key_dep.clone(), "export const foo: number = 1;");
  host.insert(key_mid.clone(), "export { foo as \"a-b\" } from \"./dep\";");
  host.insert(key_root.clone(), "export * from \"./mid\";");
  host.insert(
    key_entry.clone(),
    "import { \"a-b\" as bar } from \"./root\";\nbar satisfies number;\n",
  );
  host.link(key_mid.clone(), "./dep", key_dep.clone());
  host.link(key_root.clone(), "./mid", key_mid.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_dep = program.file_id(&key_dep).expect("dep file");
  let file_mid = program.file_id(&key_mid).expect("mid file");
  let file_root = program.file_id(&key_root).expect("root file");
  let file_entry = program.file_id(&key_entry).expect("entry file");

  let exports_dep = program.exports_of(file_dep);
  let foo = exports_dep.get("foo").expect("foo export in dep");
  assert!(foo.def.is_some());
  let foo_ty = foo.type_id.expect("type for foo");
  assert_eq!(program.display_type(foo_ty).to_string(), "number");

  let exports_mid = program.exports_of(file_mid);
  let mid_entry = exports_mid.get("a-b").expect("a-b export in mid");
  assert!(mid_entry.def.is_none());
  let mid_ty = mid_entry.type_id.expect("type for a-b in mid");
  assert_eq!(program.display_type(mid_ty).to_string(), "number");

  let exports_root = program.exports_of(file_root);
  let root_entry = exports_root.get("a-b").expect("a-b export in root");
  assert!(root_entry.def.is_none());
  let root_ty = root_entry.type_id.expect("type for a-b in root");
  assert_eq!(program.display_type(root_ty).to_string(), "number");

  let bar_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("bar"))
    .expect("imported bar def");
  let bar_ty = program.type_of_def_interned(bar_def);
  assert_eq!(program.display_type(bar_ty).to_string(), "number");
}

#[test]
fn reexport_supports_string_literal_original_names() {
  let mut host = MemoryHost::default();
  let key_dep = fk(420);
  let key_root = fk(421);
  let key_entry = fk(422);

  host.insert(
    key_dep.clone(),
    "export const foo: number = 1;\nexport { foo as \"a-b\" };",
  );
  host.insert(key_root.clone(), "export { \"a-b\" as c } from \"./dep\";");
  host.insert(
    key_entry.clone(),
    "import { c } from \"./root\";\nc satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file");
  let exports_root = program.exports_of(file_root);
  let c_entry = exports_root.get("c").expect("c export in root");
  assert!(
    c_entry.def.is_none(),
    "re-export should not point to local def"
  );
  let c_ty = c_entry.type_id.expect("type for c");
  assert_eq!(program.display_type(c_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file");
  let c_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("c"))
    .expect("imported c def");
  let c_import_ty = program.type_of_def_interned(c_def);
  assert_eq!(program.display_type(c_import_ty).to_string(), "number");
}

#[test]
fn reexport_supports_string_literal_original_and_alias_names() {
  let mut host = MemoryHost::default();
  let key_dep = fk(430);
  let key_root = fk(431);
  let key_entry = fk(432);

  host.insert(
    key_dep.clone(),
    "export const foo: number = 1;\nexport { foo as \"a-b\" };",
  );
  host.insert(
    key_root.clone(),
    "export { \"a-b\" as \"c-d\" } from \"./dep\";",
  );
  host.insert(
    key_entry.clone(),
    "import { \"c-d\" as bar } from \"./root\";\nbar satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file");
  let exports_root = program.exports_of(file_root);
  let export = exports_root.get("c-d").expect("c-d export in root");
  assert!(
    export.def.is_none(),
    "string-literal re-export should not point to local def"
  );
  let export_ty = export.type_id.expect("type for c-d");
  assert_eq!(program.display_type(export_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file");
  let bar_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("bar"))
    .expect("imported bar def");
  let bar_ty = program.type_of_def_interned(bar_def);
  assert_eq!(program.display_type(bar_ty).to_string(), "number");
}

#[test]
fn string_literal_import_name_can_be_reexported() {
  let mut host = MemoryHost::default();
  let key_dep = fk(440);
  let key_root = fk(441);
  let key_entry = fk(442);

  host.insert(
    key_dep.clone(),
    "export const foo: number = 1;\nexport { foo as \"a-b\" };",
  );
  host.insert(
    key_root.clone(),
    "import { \"a-b\" as c_d } from \"./dep\";\nexport { c_d as \"e-f\" };",
  );
  host.insert(
    key_entry.clone(),
    "import { \"e-f\" as bar } from \"./root\";\nbar satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file");
  let exports_root = program.exports_of(file_root);
  let export = exports_root.get("e-f").expect("e-f export in root");
  let export_ty = export.type_id.expect("type for e-f");
  assert_eq!(program.display_type(export_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file");
  let bar_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("bar"))
    .expect("imported bar def");
  let bar_ty = program.type_of_def_interned(bar_def);
  assert_eq!(program.display_type(bar_ty).to_string(), "number");
}

#[test]
fn string_literal_namespace_export_can_be_imported() {
  let mut host = MemoryHost::default();
  let key_dep = fk(450);
  let key_root = fk(451);
  let key_entry = fk(452);

  host.insert(
    key_dep.clone(),
    "export const value: number = 1;\nexport interface Foo { x: number; }\n",
  );
  host.insert(
    key_root.clone(),
    "export * as \"ns-name\" from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import { \"ns-name\" as ns } from \"./root\";\n\
      export const v = ns.value;\n\
      export const typed: ns.Foo = { x: 1 };\n\
      export const x = typed.x;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file");
  let exports_root = program.exports_of(file_root);
  let ns_entry = exports_root.get("ns-name").expect("ns-name export in root");
  let ns_ty = ns_entry.type_id.expect("type for ns export");
  assert_eq!(
    program.display_type(ns_ty).to_string(),
    "{ readonly value: number }"
  );

  let file_entry = program.file_id(&key_entry).expect("entry file");
  let exports_entry = program.exports_of(file_entry);
  let v_ty = exports_entry
    .get("v")
    .and_then(|entry| entry.type_id)
    .expect("type for v export");
  assert_eq!(program.display_type(v_ty).to_string(), "number");

  let x_ty = exports_entry
    .get("x")
    .and_then(|entry| entry.type_id)
    .expect("type for x export");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn default_export_can_be_reexported_as_string_literal_name() {
  let mut host = MemoryHost::default();
  let key_dep = fk(453);
  let key_root = fk(454);
  let key_entry = fk(455);

  host.insert(
    key_dep.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(
    key_root.clone(),
    "export { default as \"a-b\" } from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import { \"a-b\" as bar } from \"./root\";\nbar satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let ab_entry = exports_root.get("a-b").expect("a-b export in root");
  assert!(ab_entry.def.is_none());
  let ab_ty = ab_entry.type_id.expect("type for a-b export");
  assert_eq!(program.display_type(ab_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let bar_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("bar"))
    .expect("imported bar def");
  let bar_ty = program.type_of_def_interned(bar_def);
  assert_eq!(program.display_type(bar_ty).to_string(), "number");
}

#[test]
fn string_literal_export_can_be_reexported_as_default() {
  let mut host = MemoryHost::default();
  let key_dep = fk(456);
  let key_root = fk(457);
  let key_entry = fk(458);

  host.insert(
    key_dep.clone(),
    "export const foo: number = 1;\nexport { foo as \"a-b\" };\n",
  );
  host.insert(
    key_root.clone(),
    "export { \"a-b\" as default } from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import v from \"./root\";\nv satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let default_entry = exports_root.get("default").expect("default export in root");
  assert!(default_entry.def.is_none());
  let default_ty = default_entry.type_id.expect("type for default export");
  assert_eq!(program.display_type(default_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let v_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("imported v def");
  let v_ty = program.type_of_def_interned(v_def);
  assert_eq!(program.display_type(v_ty).to_string(), "number");
}

#[test]
fn default_import_via_named_default_specifier_can_be_reexported() {
  let mut host = MemoryHost::default();
  let key_dep = fk(500);
  let key_root = fk(501);
  let key_entry = fk(502);

  host.insert(
    key_dep.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(
    key_root.clone(),
    "import { default as a_b } from \"./dep\";\nexport { a_b as foo };\n",
  );
  host.insert(
    key_entry.clone(),
    "import { foo } from \"./root\";\nfoo satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let foo_entry = exports_root.get("foo").expect("foo export in root file");
  let foo_ty = foo_entry.type_id.expect("type for foo export");
  assert_eq!(program.display_type(foo_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let foo_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("foo"))
    .expect("imported foo def");
  let imported_foo_ty = program.type_of_def_interned(foo_def);
  assert_eq!(program.display_type(imported_foo_ty).to_string(), "number");
}

#[test]
fn default_import_via_named_default_specifier_can_be_exported_as_default() {
  let mut host = MemoryHost::default();
  let key_dep = fk(510);
  let key_root = fk(511);
  let key_entry = fk(512);

  host.insert(
    key_dep.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(
    key_root.clone(),
    "import { default as a_b } from \"./dep\";\nexport { a_b as default };\n",
  );
  host.insert(
    key_entry.clone(),
    "import v from \"./root\";\nv satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let default_entry = exports_root
    .get("default")
    .expect("default export in root file");
  let default_ty = default_entry.type_id.expect("type for default export");
  assert_eq!(program.display_type(default_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let v_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("imported v def");
  let v_ty = program.type_of_def_interned(v_def);
  assert_eq!(program.display_type(v_ty).to_string(), "number");
}

#[test]
fn default_export_has_type() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("default.ts");
  host.insert(key.clone(), "export default 42;");

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
  let default_entry = exports.get("default").expect("default export");
  assert!(default_entry.def.is_some());
  let ty = default_entry.type_id.expect("type for default");
  assert_eq!(program.display_type(ty).to_string(), "42");
}

#[test]
fn default_export_can_be_reexported_under_new_name() {
  let mut host = MemoryHost::default();
  let key_dep = fk(460);
  let key_root = fk(461);
  let key_entry = fk(462);

  host.insert(
    key_dep.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(
    key_root.clone(),
    "export { default as foo } from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import { foo } from \"./root\";\nfoo satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let foo_entry = exports_root.get("foo").expect("foo export in root file");
  assert!(foo_entry.def.is_none());
  let foo_ty = foo_entry.type_id.expect("type for foo export");
  assert_eq!(program.display_type(foo_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let foo_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("foo"))
    .expect("imported foo def");
  let foo_import_ty = program.type_of_def_interned(foo_def);
  assert_eq!(program.display_type(foo_import_ty).to_string(), "number");
}

#[test]
fn named_export_can_be_reexported_as_default() {
  let mut host = MemoryHost::default();
  let key_dep = fk(470);
  let key_root = fk(471);
  let key_entry = fk(472);

  host.insert(key_dep.clone(), "export const foo: number = 1;\n");
  host.insert(
    key_root.clone(),
    "export { foo as default } from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import v from \"./root\";\nv satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let default_entry = exports_root
    .get("default")
    .expect("default export in root file");
  assert!(default_entry.def.is_none());
  let default_ty = default_entry.type_id.expect("type for default export");
  assert_eq!(program.display_type(default_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let v_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("imported v def");
  let v_ty = program.type_of_def_interned(v_def);
  assert_eq!(program.display_type(v_ty).to_string(), "number");
}

#[test]
fn default_export_can_be_imported_via_named_default_specifier() {
  let mut host = MemoryHost::default();
  let key_module = fk(480);
  let key_entry = fk(481);

  host.insert(
    key_module.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(
    key_entry.clone(),
    "import { default as foo } from \"./m\";\nfoo satisfies number;\n",
  );
  host.link(key_entry.clone(), "./m", key_module.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let foo_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("foo"))
    .expect("imported foo def");
  let foo_ty = program.type_of_def_interned(foo_def);
  assert_eq!(program.display_type(foo_ty).to_string(), "number");
}

#[test]
fn named_export_can_be_exported_as_default_locally() {
  let mut host = MemoryHost::default();
  let key_module = fk(490);
  let key_entry = fk(491);

  host.insert(
    key_module.clone(),
    "export const foo: number = 1;\nexport { foo as default };\n",
  );
  host.insert(
    key_entry.clone(),
    "import v from \"./m\";\nv satisfies number;\n",
  );
  host.link(key_entry.clone(), "./m", key_module.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_module = program.file_id(&key_module).expect("module file id");
  let exports_module = program.exports_of(file_module);
  let default_entry = exports_module
    .get("default")
    .expect("default export in module file");
  let default_ty = default_entry.type_id.expect("type for default export");
  assert_eq!(program.display_type(default_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let v_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("imported v def");
  let v_ty = program.type_of_def_interned(v_def);
  assert_eq!(program.display_type(v_ty).to_string(), "number");
}

#[test]
fn default_export_follows_reexport_specifier_chain() {
  let mut host = MemoryHost::default();
  let key_dep = fk(223);
  let key_root = fk(224);
  let key_entry = fk(225);

  host.insert(
    key_dep.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(key_root.clone(), "export { default } from \"./dep\";\n");
  host.insert(
    key_entry.clone(),
    "import v from \"./root\";\nexport const x = v;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let default_entry = exports_root
    .get("default")
    .expect("default export in root file");
  assert!(default_entry.def.is_none());
  let default_ty = default_entry.type_id.expect("type for default export");
  assert_eq!(program.display_type(default_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry file id");
  let exports_entry = program.exports_of(file_entry);
  let x_ty = exports_entry
    .get("x")
    .and_then(|entry| entry.type_id)
    .expect("type for x export");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn export_const_initializer_infers_type() {
  let mut host = MemoryHost::default();
  let entry = FileKey::new("index.ts");
  let math = FileKey::new("math.ts");
  host.insert(
    entry.clone(),
    "import { add } from \"./math\";\nexport const total = add(1, 2);",
  );
  host.insert(
    math.clone(),
    "export function add(a: number, b: number): number { return a + b; }",
  );
  host.link(entry.clone(), "./math", math.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id");
  let exports = program.exports_of(file_id);
  let total = exports.get("total").expect("total export");
  let ty = total.type_id.expect("type for total");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn shadowed_bindings_map_to_distinct_initializers() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("shadow.ts");
  let source =
    "function outer() { const value = 2; return value; }\nconst value = 1;\nexport { outer, value };";
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let mut inits: Vec<_> = program
    .definitions_in_file(file_id)
    .into_iter()
    .filter(|def| program.def_name(*def).as_deref() == Some("value"))
    .filter_map(|def| program.var_initializer(def))
    .collect();
  // `definitions_in_file` includes both the binding (`Var`) and its enclosing
  // `VarDeclarator` definition. Both map to the same initializer body/expression,
  // so normalize to distinct initializers before asserting.
  inits.sort_by_key(|init| (init.body.0, init.expr.0));
  inits.dedup_by_key(|init| (init.body, init.expr));
  assert_eq!(inits.len(), 2, "expected two distinct value initializers");
  inits.sort_by_key(|init| init.span.map(|span| span.start).unwrap_or(u32::MAX));

  let inner_init = inits[0];
  let outer_init = inits[1];
  assert_ne!(inner_init.body, outer_init.body);
  let inner_span = program
    .expr_span(inner_init.body, inner_init.expr)
    .expect("inner expr span");
  let outer_span = program
    .expr_span(outer_init.body, outer_init.expr)
    .expect("outer expr span");
  let inner_text = &source[inner_span.range.start as usize..inner_span.range.end as usize];
  let outer_text = &source[outer_span.range.start as usize..outer_span.range.end as usize];
  assert_eq!(inner_text, "2");
  assert_eq!(outer_text, "1");
}

#[test]
fn default_export_expr_resolves_for_default_imports() {
  let mut host = MemoryHost::default();
  let key_module = fk(300);
  let key_entry = fk(301);
  host.insert(
    key_module.clone(),
    "const x = 1;\nexport const named = 2;\nexport default x;\n",
  );
  host.insert(
    key_entry.clone(),
    "import foo from \"./m\";\nimport { named } from \"./m\";\nfoo satisfies number;\nnamed satisfies number;\n",
  );
  host.link(key_entry.clone(), "./m", key_module.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let module_id = program.file_id(&key_module).expect("module id");
  let exports = program.exports_of(module_id);
  let default_entry = exports.get("default").expect("default export present");
  assert!(
    default_entry.def.is_some(),
    "default export should be visible to semantic exports"
  );
  let default_ty = default_entry.type_id.expect("type for default");
  let rendered = program.display_type(default_ty).to_string();
  assert!(
    rendered == "1" || rendered == "number",
    "unexpected default export type: {rendered}"
  );
  assert!(
    exports.contains_key("named"),
    "expected named export to remain available"
  );
}

#[test]
fn type_exports_propagate_through_reexports() {
  let mut host = MemoryHost::default();
  let key_types = fk(20);
  let key_entry = fk(21);
  host.insert(key_types.clone(), "export type Foo = { a: string };");
  host.insert(key_entry.clone(), "export type { Foo } from \"./types\";");
  host.link(key_entry.clone(), "./types", key_types.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&key_entry).expect("entry id");
  let exports_types = program.exports_of(entry_id);
  let foo = exports_types.get("Foo").expect("Foo type export");
  assert!(foo.def.is_none(), "re-export should not point to local def");
  let foo_ty = foo.type_id.expect("type for Foo");
  let rendered = program.display_type(foo_ty).to_string();
  // Either the alias name is preserved or the object structure is shown
  assert!(
    rendered == "Foo" || rendered.contains("a: string"),
    "expected Foo alias or object type with a: string, got {rendered}"
  );
}

#[test]
fn exports_support_string_literal_names() {
  let mut host = MemoryHost::default();
  let key_mod = fk(400);
  let key_entry = fk(401);
  host.insert(
    key_mod.clone(),
    "export const foo: number = 1;\nexport { foo as \"a-b\" };",
  );
  host.insert(
    key_entry.clone(),
    "import { \"a-b\" as bar } from \"./mod\";\nbar satisfies number;\n",
  );
  host.link(key_entry.clone(), "./mod", key_mod.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_mod = program.file_id(&key_mod).expect("module id");
  let exports_mod = program.exports_of(file_mod);
  let export = exports_mod.get("a-b").expect("export a-b present");
  let export_ty = export.type_id.expect("type for export a-b");
  assert_eq!(program.display_type(export_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry id");
  let bar_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("bar"))
    .expect("imported bar def");
  let bar_ty = program.type_of_def_interned(bar_def);
  assert_eq!(program.display_type(bar_ty).to_string(), "number");
}

#[test]
fn type_exports_support_string_literal_names() {
  let mut host = MemoryHost::default();
  let key_mod = fk(460);
  let key_entry = fk(461);
  host.insert(
    key_mod.clone(),
    "export type Foo = number;\nexport type { Foo as \"a-b\" };",
  );
  host.insert(
    key_entry.clone(),
    "import type { \"a-b\" as Bar } from \"./mod\";\n\
     declare const x: Bar;\n\
     x satisfies number;\n",
  );
  host.link(key_entry.clone(), "./mod", key_mod.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_mod = program.file_id(&key_mod).expect("module id");
  let exports_mod = program.exports_of(file_mod);
  let export = exports_mod.get("a-b").expect("export a-b present");
  let export_ty = export.type_id.expect("type for export a-b");
  let rendered = program.display_type(export_ty).to_string();
  assert!(
    rendered == "Foo" || rendered == "number",
    "unexpected type export for a-b: {rendered}"
  );

  let file_entry = program.file_id(&key_entry).expect("entry id");
  let bar_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Bar"))
    .expect("imported Bar def");
  let bar_ty = program.type_of_def_interned(bar_def);
  let bar_rendered = program.display_type(bar_ty).to_string();
  assert!(
    bar_rendered == "Foo" || bar_rendered == "number",
    "unexpected type for imported Bar: {bar_rendered}"
  );
}

#[test]
fn type_only_default_export_can_be_reexported_as_string_literal_name() {
  let mut host = MemoryHost::default();
  let key_dep = fk(520);
  let key_root = fk(521);
  let key_entry = fk(522);

  host.insert(
    key_dep.clone(),
    "const value: number = 1;\nexport default value;\n",
  );
  host.insert(
    key_root.clone(),
    "export type { default as \"a-b\" } from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import type { \"a-b\" as Foo } from \"./root\";\n\
     declare const x: Foo;\n\
     x satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let ab_entry = exports_root.get("a-b").expect("a-b export in root file");
  assert!(ab_entry.def.is_none());
  let ab_ty = ab_entry.type_id.expect("type for a-b export");
  assert_eq!(program.display_type(ab_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry id");
  let foo_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Foo"))
    .expect("imported Foo def");
  let foo_ty = program.type_of_def_interned(foo_def);
  assert_eq!(program.display_type(foo_ty).to_string(), "number");
}

#[test]
fn type_only_string_export_can_be_reexported_as_default() {
  let mut host = MemoryHost::default();
  let key_dep = fk(530);
  let key_root = fk(531);
  let key_entry = fk(532);

  host.insert(
    key_dep.clone(),
    "export const foo: number = 1;\nexport { foo as \"a-b\" };\n",
  );
  host.insert(
    key_root.clone(),
    "export type { \"a-b\" as default } from \"./dep\";\n",
  );
  host.insert(
    key_entry.clone(),
    "import type v from \"./root\";\n\
     declare const x: v;\n\
     x satisfies number;\n",
  );
  host.link(key_root.clone(), "./dep", key_dep.clone());
  host.link(key_entry.clone(), "./root", key_root.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_root = program.file_id(&key_root).expect("root file id");
  let exports_root = program.exports_of(file_root);
  let default_entry = exports_root
    .get("default")
    .expect("default export in root file");
  assert!(default_entry.def.is_none());
  let default_ty = default_entry.type_id.expect("type for default export");
  assert_eq!(program.display_type(default_ty).to_string(), "number");

  let file_entry = program.file_id(&key_entry).expect("entry id");
  let v_def = program
    .definitions_in_file(file_entry)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("v"))
    .expect("imported v def");
  let v_ty = program.type_of_def_interned(v_def);
  assert_eq!(program.display_type(v_ty).to_string(), "number");
}

#[test]
fn export_star_cycle_reaches_fixpoint() {
  let mut host = MemoryHost::default();
  let key_a = fk(210);
  let key_b = fk(211);
  let key_c = fk(212);
  host.insert(
    key_a.clone(),
    "export * from \"./b\";\nexport * from \"./c\";",
  );
  host.insert(key_b.clone(), "export * from \"./a\";");
  host.insert(key_c.clone(), "export const shared = 1;");
  host.link(key_a.clone(), "./b", key_b.clone());
  host.link(key_a.clone(), "./c", key_c.clone());
  host.link(key_b.clone(), "./a", key_a.clone());

  let program = Program::new(host, vec![key_a.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  for key in [key_a, key_b, key_c] {
    let file = program.file_id(&key).expect("file id");
    let exports = program.exports_of(file);
    let shared = exports.get("shared").expect("shared export present");
    let ty = shared.type_id.expect("type for shared");
    assert_eq!(program.display_type(ty).to_string(), "1");
  }
}

#[test]
fn export_star_skips_default() {
  let mut host = MemoryHost::default();
  let key_a = fk(220);
  let key_b = fk(221);
  host.insert(key_a.clone(), "export default 1;\nexport const named = 2;");
  host.insert(key_b.clone(), "export * from \"./a\";");
  host.link(key_b.clone(), "./a", key_a.clone());

  let program = Program::new(host, vec![key_b.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_b = program.file_id(&key_b).expect("file id");
  let exports = program.exports_of(file_b);
  assert!(
    !exports.contains_key("default"),
    "default should not be re-exported"
  );
  let named = exports.get("named").expect("named export propagated");
  let ty = named.type_id.expect("type for named");
  assert_eq!(program.display_type(ty).to_string(), "2");
}

#[test]
fn imported_overloads_preserve_all_signatures() {
  let mut host = MemoryHost::default();
  let key_math = fk(310);
  let key_use = fk(311);
  host.insert(
    key_math.clone(),
    "export function overload(value: string): string;\n\
     export function overload(value: number): number;\n\
     export function overload(value: string | number) { return value; }",
  );
  host.insert(
    key_use.clone(),
    "import { overload } from \"./math\";\n\
     export const asString = overload(\"hi\");\n\
      export const asNumber = overload(1);",
  );
  host.link(key_use.clone(), "./math", key_math.clone());

  let program = Program::new(host, vec![key_use.clone()]);
  let diagnostics = program.check();
  let math_id = program.file_id(&key_math).expect("math id");
  let math_exports = program.exports_of(math_id);
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let overload_entry = math_exports.get("overload").expect("overload export");
  let overload_type = overload_entry.type_id.expect("type for overload");
  let returns: Vec<_> = program
    .call_signatures(overload_type)
    .iter()
    .map(|sig| program.display_type(sig.signature.ret).to_string())
    .collect();
  assert!(
    returns.contains(&"string".to_string()) && returns.contains(&"number".to_string()),
    "expected overloads for string and number, got {returns:?}"
  );

  let use_id = program.file_id(&key_use).expect("use id");
  let use_exports = program.exports_of(use_id);
  let str_def = use_exports
    .get("asString")
    .and_then(|entry| entry.def)
    .expect("asString def");
  let num_def = use_exports
    .get("asNumber")
    .and_then(|entry| entry.def)
    .expect("asNumber def");
  assert_eq!(
    program
      .display_type(program.type_of_def(str_def))
      .to_string(),
    "string"
  );
  assert_eq!(
    program
      .display_type(program.type_of_def(num_def))
      .to_string(),
    "number"
  );
}

#[test]
fn typeof_imported_overload_merges_signatures() {
  let mut host = MemoryHost::default();
  let key_math = fk(320);
  let key_use = fk(321);
  host.insert(
    key_math.clone(),
    "export function overload(value: string): string;\n\
     export function overload(value: number): number;\n\
     export function overload(value: string | number) { return value; }",
  );
  host.insert(
    key_use.clone(),
    "import { overload } from \"./math\";\n\
     type Over = typeof overload;\n\
      const fn: Over = overload;\n\
     export const viaString = fn(\"hi\");\n\
     export const viaNumber = fn(2);",
  );
  host.link(key_use.clone(), "./math", key_math.clone());

  let program = Program::new(host, vec![key_use.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let use_id = program.file_id(&key_use).expect("use id");
  let exports = program.exports_of(use_id);

  let via_string = exports
    .get("viaString")
    .expect("string overload call export");
  let via_string_def = via_string.def.expect("viaString def");
  assert_eq!(
    program
      .display_type(program.type_of_def(via_string_def))
      .to_string(),
    "string"
  );

  let via_number = exports
    .get("viaNumber")
    .expect("number overload call export");
  let via_number_def = via_number.def.expect("viaNumber def");
  assert_eq!(
    program
      .display_type(program.type_of_def(via_number_def))
      .to_string(),
    "number"
  );
}

#[test]
fn duplicate_export_reports_conflict() {
  let mut host = MemoryHost::default();
  let key_a = fk(230);
  let key_b = fk(231);
  let key_c = fk(232);
  host.insert(key_a.clone(), "export const foo = 1;");
  host.insert(key_b.clone(), "export function foo(): number { return 2; }");
  host.insert(
    key_c.clone(),
    "export * from \"./a\";\nexport { foo } from \"./b\";",
  );
  host.link(key_c.clone(), "./a", key_a.clone());
  host.link(key_c.clone(), "./b", key_b.clone());

  let program = Program::new(host, vec![key_c.clone()]);
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1, "expected a conflict diagnostic");
  assert_eq!(diagnostics[0].code.as_str(), "BIND1001");
  let file_c = program.file_id(&key_c).expect("file c");
  assert_eq!(diagnostics[0].primary.file, file_c);
}

#[test]
fn namespace_exports_include_namespace_slot() {
  let mut host = MemoryHost::default();
  let key = fk(30);
  host.insert(
    key.clone(),
    "export function foo() { return 1; }\nexport namespace foo { }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
  let value_entry = exports.get("foo").expect("value export foo");
  assert!(
    value_entry.type_id.is_some(),
    "merged namespace/value should carry a type"
  );
}

#[test]
fn export_star_conflict_reports_diagnostic() {
  let mut host = MemoryHost::default();
  let key_one = fk(100);
  let key_two = fk(101);
  let key_entry = fk(102);
  host.insert(key_one.clone(), "export const dup = 1;");
  host.insert(key_two.clone(), "export const dup = 2;");
  host.insert(
    key_entry.clone(),
    "export * from \"./one\";\nexport * from \"./two\";",
  );
  host.link(key_entry.clone(), "./one", key_one.clone());
  host.link(key_entry.clone(), "./two", key_two.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1, "expected conflict diagnostic");
  assert_eq!(diagnostics[0].code.as_str(), "BIND1001");
}

#[test]
fn export_namespace_all_is_supported() {
  let mut host = MemoryHost::default();
  let key_a = fk(300);
  let key_b = fk(301);
  host.insert(key_a.clone(), "export const a: number = 1;");
  host.insert(key_b.clone(), "export * as ns from \"./a\";");
  host.link(key_b.clone(), "./a", key_a.clone());

  let program = Program::new(host, vec![key_b.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_b = program.file_id(&key_b).expect("file b");
  let exports = program.exports_of(file_b);
  let ns_entry = exports.get("ns").expect("ns export");
  assert!(
    ns_entry.def.is_none(),
    "namespace re-export should not bind a local def"
  );
  let ns_ty = ns_entry.type_id.expect("type for ns");
  assert_eq!(
    program.display_type(ns_ty).to_string(),
    "{ readonly a: number }",
    "ns should be typed as a module namespace object of the target's value exports"
  );
}

#[test]
fn unresolved_export_points_at_specifier() {
  let mut host = MemoryHost::default();
  let source = r#"export * from "./missing";"#;
  let key = fk(350);
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert_eq!(
    diagnostics.len(),
    1,
    "expected unresolved module diagnostic, got {diagnostics:?}"
  );
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::UNRESOLVED_MODULE.as_str());
  let file_id = program.file_id(&key).expect("file id");
  assert_eq!(diag.primary.file, file_id);

  let specifier = "\"./missing\"";
  let start = source.find(specifier).expect("missing specifier in source") as u32;
  let end = start + specifier.len() as u32;
  let expected_span = TextRange::new(start, end);
  assert!(
    diag.primary.range.start <= expected_span.start && diag.primary.range.end >= expected_span.end,
    "diagnostic span {:?} should cover specifier {:?}",
    diag.primary.range,
    expected_span
  );
}

#[test]
fn interned_type_for_exported_function() {
  let mut host = MemoryHost::default();
  let key = fk(50);
  host.insert(
    key.clone(),
    "export function add(a: number, b: number): number { return a + b; }",
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
    .find(|d| program.def_name(*d).as_deref() == Some("add"))
    .expect("add definition");
  let ty = program.type_of_def(def);
  assert_eq!(
    program.display_type(ty).to_string(),
    "(number, number) => number"
  );
}

#[test]
fn recursive_type_alias_produces_ref() {
  let mut host = MemoryHost::default();
  let key = fk(40);
  host.insert(key.clone(), "type Node = Node;");

  let program = Program::new(host, vec![key.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Node"))
    .expect("Node alias");
  let ty = program.type_of_def(def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("Node"),
    "expected recursive alias to render as Node, got {rendered}"
  );
}
