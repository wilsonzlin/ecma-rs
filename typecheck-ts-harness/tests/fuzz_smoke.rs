use std::sync::Arc;
use std::time::{Duration, Instant};

use serde_json::{Map, Value};
use typecheck_ts::FileKey;
use typecheck_ts_harness::runner::HarnessFileSet;
use typecheck_ts_harness::VirtualFile;

struct Lcg(u64);

impl Lcg {
  fn next_u32(&mut self) -> u32 {
    self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
    (self.0 >> 32) as u32
  }

  fn next_usize(&mut self, max_exclusive: usize) -> usize {
    if max_exclusive == 0 {
      return 0;
    }
    (self.next_u32() as usize) % max_exclusive
  }

  fn next_bool(&mut self) -> bool {
    self.next_u32() & 1 == 1
  }
}

fn random_json_value(rng: &mut Lcg, depth: usize) -> Value {
  if depth == 0 {
    return match rng.next_u32() % 5 {
      0 => Value::Null,
      1 => Value::Bool(rng.next_bool()),
      2 => Value::Number(serde_json::Number::from((rng.next_u32() % 128) as u64)),
      3 => Value::String(format!("s{}", rng.next_u32() % 16)),
      _ => Value::Array(Vec::new()),
    };
  }

  match rng.next_u32() % 7 {
    0 => Value::Null,
    1 => Value::Bool(rng.next_bool()),
    2 => Value::Number(serde_json::Number::from((rng.next_u32() % 4096) as u64)),
    3 => Value::String(format!("str{}", rng.next_u32())),
    4 => {
      let len = rng.next_usize(4);
      let mut arr = Vec::with_capacity(len);
      for _ in 0..len {
        arr.push(random_json_value(rng, depth - 1));
      }
      Value::Array(arr)
    }
    _ => {
      let len = rng.next_usize(4);
      let mut obj = Map::new();
      for idx in 0..len {
        obj.insert(
          format!("k{idx}_{}", rng.next_u32() % 8),
          random_json_value(rng, depth - 1),
        );
      }
      Value::Object(obj)
    }
  }
}

fn package_json_with_exports(rng: &mut Lcg) -> Value {
  let mut obj = Map::new();
  obj.insert("name".into(), Value::String("pkg".into()));

  // Randomize `exports` with both valid and invalid shapes.
  let exports = match rng.next_u32() % 4 {
    0 => Value::String("./index.d.ts".into()),
    1 => {
      let mut exports_obj = Map::new();
      exports_obj.insert(".".into(), Value::String("./index.d.ts".into()));
      exports_obj.insert("./subpath".into(), Value::String("./subpath.d.ts".into()));
      exports_obj.insert("./*".into(), Value::String("./*.d.ts".into()));
      Value::Object(exports_obj)
    }
    2 => Value::Array(vec![
      Value::String("./index.d.ts".into()),
      random_json_value(rng, 2),
    ]),
    _ => random_json_value(rng, 3),
  };
  obj.insert("exports".into(), exports);
  Value::Object(obj)
}

fn root_package_json_with_imports(rng: &mut Lcg) -> Value {
  let mut obj = Map::new();
  let imports = match rng.next_u32() % 3 {
    0 => {
      let mut imports_obj = Map::new();
      imports_obj.insert("#alias".into(), Value::String("./src/local".into()));
      imports_obj.insert("#alias/*".into(), Value::String("./src/*".into()));
      Value::Object(imports_obj)
    }
    1 => random_json_value(rng, 2),
    _ => Value::Null,
  };
  obj.insert("imports".into(), imports);
  Value::Object(obj)
}

fn maybe_invalid_json(rng: &mut Lcg, value: Value) -> String {
  if rng.next_u32() % 6 == 0 {
    // Intentionally malformed.
    "not json".into()
  } else {
    serde_json::to_string(&value).unwrap_or_else(|_| "{}".into())
  }
}

#[test]
#[ignore]
fn fuzz_smoke_resolver() {
  let mut rng = Lcg(0xc2b2_ae3d_27d4_eb4f);
  let start = Instant::now();
  let mut iters = 0usize;

  while iters < 10_000 && start.elapsed() < Duration::from_secs(3) {
    let root_pkg_value = root_package_json_with_imports(&mut rng);
    let root_pkg = maybe_invalid_json(&mut rng, root_pkg_value);
    let pkg_pkg_value = package_json_with_exports(&mut rng);
    let pkg_pkg = maybe_invalid_json(&mut rng, pkg_pkg_value);

    let files = vec![
      VirtualFile {
        name: "/project/src/index.ts".into(),
        content: Arc::from("export {};"),
      },
      VirtualFile {
        name: "/project/src/local.ts".into(),
        content: Arc::from("export const x = 1;"),
      },
      VirtualFile {
        name: "/project/src/subpath.d.ts".into(),
        content: Arc::from("export {};"),
      },
      VirtualFile {
        name: "/project/package.json".into(),
        content: Arc::from(root_pkg),
      },
      VirtualFile {
        name: "/project/node_modules/pkg/package.json".into(),
        content: Arc::from(pkg_pkg),
      },
      VirtualFile {
        name: "/project/node_modules/pkg/index.d.ts".into(),
        content: Arc::from("export {};"),
      },
      VirtualFile {
        name: "/project/node_modules/pkg/subpath.d.ts".into(),
        content: Arc::from("export {};"),
      },
      VirtualFile {
        name: "/project/node_modules/@types/pkg/index.d.ts".into(),
        content: Arc::from("export {};"),
      },
    ];

    let spec = match rng.next_u32() % 6 {
      0 => "./local".to_string(),
      1 => "./local.ts".to_string(),
      2 => "#alias".to_string(),
      3 => "pkg".to_string(),
      4 => "pkg/subpath".to_string(),
      _ => "/project/src/local.ts".to_string(),
    };

    let from = FileKey::new("/project/src/index.ts");
    let set = HarnessFileSet::new(&files);
    let first = set.resolve_import(&from, &spec);
    let second = set.resolve_import(&from, &spec);
    assert_eq!(first, second, "resolver output must be deterministic");

    let mut reversed = files.clone();
    reversed.reverse();
    let set2 = HarnessFileSet::new(&reversed);
    let third = set2.resolve_import(&from, &spec);
    assert_eq!(
      first, third,
      "resolver output must be stable across input ordering"
    );

    iters += 1;
  }
}
