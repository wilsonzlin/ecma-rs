use typecheck_ts::FileKey;
use typecheck_ts_harness::module_resolution::ModuleResolver;
use typecheck_ts_harness::runner::HarnessFileSet;
use typecheck_ts_harness::VirtualFile;

#[test]
fn resolves_package_json_types_entrypoints() {
  let files = vec![
    VirtualFile {
      name: "/src/app.ts".to_string(),
      content: "import \"pkg\";\n".to_string(),
    },
    VirtualFile {
      name: "/node_modules/pkg/package.json".to_string(),
      content: r#"{ "types": "./dist/index.d.ts" }"#.to_string(),
    },
    VirtualFile {
      name: "/node_modules/pkg/dist/index.d.ts".to_string(),
      content: "export {};\n".to_string(),
    },
  ];

  let file_set = HarnessFileSet::new(&files);
  let resolver = ModuleResolver::new();

  let resolved = resolver.resolve(&file_set, &FileKey::new("/src/app.ts"), "pkg");
  assert_eq!(
    resolved,
    Some(FileKey::new("/node_modules/pkg/dist/index.d.ts"))
  );
}

#[test]
fn resolves_package_json_exports_types_entrypoints() {
  let files = vec![
    VirtualFile {
      name: "/src/app.ts".to_string(),
      content: "import \"pkg\";\n".to_string(),
    },
    VirtualFile {
      name: "/node_modules/pkg/package.json".to_string(),
      content: r#"{ "exports": { ".": { "types": "./dist/index.d.ts" } } }"#.to_string(),
    },
    VirtualFile {
      name: "/node_modules/pkg/dist/index.d.ts".to_string(),
      content: "export {};\n".to_string(),
    },
  ];

  let file_set = HarnessFileSet::new(&files);
  let resolver = ModuleResolver::new();

  let resolved = resolver.resolve(&file_set, &FileKey::new("/src/app.ts"), "pkg");
  assert_eq!(
    resolved,
    Some(FileKey::new("/node_modules/pkg/dist/index.d.ts"))
  );
}
