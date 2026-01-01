use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileId, FileKey, MemoryHost, Program};

#[test]
fn reachable_files_are_stable_and_cycle_safe() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    include_dom: false,
    no_default_lib: true,
    ..Default::default()
  });
  let entry = FileKey::new("file0.ts");
  let dep = FileKey::new("file1.ts");
  let tail = FileKey::new("file2.ts");

  host.insert(entry.clone(), "import \"./file1\";");
  host.insert(dep.clone(), "import \"./file2\";");
  host.insert(tail.clone(), "import \"./file0\"; export const value = 1;");

  host.link(entry.clone(), "./file1", dep.clone());
  host.link(dep.clone(), "./file2", tail.clone());
  host.link(tail.clone(), "./file0", entry.clone());

  let program = Program::new(host.clone(), vec![entry.clone()]);
  let reachable = program.reachable_files();
  assert_eq!(reachable, vec![FileId(0), FileId(1), FileId(2)]);

  let program_reordered = Program::new(host, vec![tail.clone(), dep.clone(), entry]);
  let reordered = program_reordered.reachable_files();
  assert_eq!(reachable, reordered);
}

#[test]
fn reachable_files_include_type_import_deps() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    include_dom: false,
    no_default_lib: true,
    ..Default::default()
  });
  // Use deterministic test IDs (`file{N}.ts` -> `FileId(N)`) so we can assert
  // exact ordering.
  let entry = FileKey::new("file0.ts");
  let dep = FileKey::new("file1.ts");

  host.insert(
    entry.clone(),
    r#"
type Foo = import("./file1").Foo;
type Bar = typeof import("./file1").Foo;
"#,
  );
  host.insert(dep.clone(), "export interface Foo {}");

  host.link(entry.clone(), "./file1", dep.clone());

  let program = Program::new(host, vec![entry]);
  let reachable = program.reachable_files();
  assert_eq!(
    reachable,
    vec![FileId(0), FileId(1)],
    "module graph should include deps introduced only via import() types"
  );
}
