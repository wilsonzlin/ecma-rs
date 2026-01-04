use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[derive(Clone, Debug)]
struct Rng(u64);

impl Rng {
  fn new(seed: u64) -> Self {
    Self(seed)
  }

  fn next_u64(&mut self) -> u64 {
    // xorshift64*
    let mut x = self.0;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    self.0 = x;
    x.wrapping_mul(0x2545_f491_4f6c_dd1d)
  }

  fn gen_usize(&mut self, upper: usize) -> usize {
    debug_assert!(upper > 0);
    (self.next_u64() as usize) % upper
  }
}

fn fragment(rng: &mut Rng, id: u32) -> String {
  match rng.gen_usize(14) {
    0 => format!(
      "type Lit{id} = \"a\" | \"b\" | \"c\";\nconst v{id}: Lit{id} = \"a\";\n"
    ),
    1 => format!(
      "type Box{id}<T> = {{ value: T }};\nconst b{id}: Box{id}<number> = {{ value: 1 }};\n"
    ),
    2 => format!(
      "type Node{id} = {{ next?: Node{id}; value: number }};\nconst n{id}: Node{id} = {{ value: 1 }};\n"
    ),
    3 => format!(
      "type RecCond{id}<T> = T extends string ? RecCond{id}<T> : T;\ntype RCUse{id} = RecCond{id}<string>;\n"
    ),
    4 => format!(
      "type Keys{id}<T> = keyof T;\ntype KeyUse{id} = Keys{id}<{{ a: number; b: string }}>;\n"
    ),
    5 => format!(
      "type Map{id}<T> = {{ [K in keyof T]: T[K] }};\ntype MapUse{id} = Map{id}<{{ a: number; b: string }}>;\nconst m{id}: MapUse{id} = {{ a: 1, b: \"x\" }};\n"
    ),
    6 => format!(
      "type Ro{id}<T> = {{ readonly [K in keyof T]: T[K] }};\ntype RoUse{id} = Ro{id}<{{ a: number; b: string }}>;\nconst ro{id}: RoUse{id} = {{ a: 1, b: \"x\" }};\n"
    ),
    7 => format!(
      "type TL{id}<T extends string> = `${{T}}_{id}`;\ntype TLUse{id} = TL{id}<\"a\" | \"b\">;\nconst tl{id}: TLUse{id} = \"a_{id}\";\n"
    ),
    8 => format!(
      "type Obj{id} = {{ a: number; b?: string }};\ntype Val{id} = Obj{id}[\"a\" | \"b\"];\nconst val{id}: Val{id} = 1;\n"
    ),
    9 => {
      let arg = rng.gen_usize(4);
      format!(
        "function id{id}<T>(x: T): T {{ return x; }}\nconst res{id} = id{id}({arg});\n"
      )
    }
    10 => {
      let arg = rng.gen_usize(4);
      format!(
        "class C{id}<T> {{ value: T; constructor(value: T) {{ this.value = value; }} }}\nconst c{id} = new C{id}({arg});\n"
      )
    }
    11 => format!("const bad{id}: number = \"x\";\n"),
    12 => format!(
      "type Infer{id}<T> = T extends infer U ? U : never;\ntype InferUse{id} = Infer{id}<string>;\n"
    ),
    13 => format!(
      "type Remap{id}<T> = {{ [K in keyof T as `${{K & string}}_done`]: T[K] }};\ntype RemapUse{id} = Remap{id}<{{ a: number }}>;\n"
    ),
    _ => unreachable!("rng.gen_usize is bounded"),
  }
}

fn generate_program(rng: &mut Rng, case: usize) -> String {
  let mut out = String::new();
  out.push_str("export {};\n");

  let fragment_count = 5 + rng.gen_usize(8);
  for idx in 0..fragment_count {
    let id = (case as u32) * 100 + idx as u32;
    out.push_str(&fragment(rng, id));
  }
  out
}

fn run_with_timeout(case: usize, source: &str, timeout: Duration) -> Vec<typecheck_ts::Diagnostic> {
  let options = CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  };
  let mut host = MemoryHost::with_options(options);
  let file = FileKey::new(format!("case_{case}.ts"));
  host.insert(file.clone(), Arc::<str>::from(source.to_string()));

  let program = Arc::new(Program::new(host, vec![file]));
  let runner = Arc::clone(&program);
  let handle = thread::spawn(move || runner.check());

  let started_at = Instant::now();
  let deadline = started_at + timeout;
  while Instant::now() < deadline {
    if handle.is_finished() {
      break;
    }
    thread::sleep(Duration::from_millis(5));
  }

  if !handle.is_finished() {
    program.cancel();
    let cancel_timeout = Duration::from_millis(500);
    let cancel_deadline = Instant::now() + cancel_timeout;
    while Instant::now() < cancel_deadline {
      if handle.is_finished() {
        break;
      }
      thread::sleep(Duration::from_millis(5));
    }
    if !handle.is_finished() {
      eprintln!(
        "case {case}: checker did not observe cancellation within {:?}; exiting to avoid hanging tests",
        cancel_timeout
      );
      std::process::exit(1);
    }
    let _ = handle
      .join()
      .expect("checker thread panicked after cancellation");
    panic!(
      "case {case}: Program::check did not finish within {:?}",
      timeout
    );
  }

  handle.join().expect("checker thread panicked")
}

#[test]
fn fuzz_smoke_program_check_is_total_and_fast() {
  const CASES: usize = 32;
  const SEED: u64 = 0x9d3d_6f5c_2b4a_1c87;
  const TIMEOUT: Duration = Duration::from_millis(250);

  let mut rng = Rng::new(SEED);
  for case in 0..CASES {
    let program = generate_program(&mut rng, case);
    let mut diagnostics = run_with_timeout(case, &program, TIMEOUT);
    codes::normalize_diagnostics(&mut diagnostics);

    assert!(
      diagnostics
        .iter()
        .all(|diag| !diag.code.as_str().starts_with("ICE")),
      "case {case}: checker emitted ICE diagnostics\nsource:\n{program}\n\ndiagnostics:\n{diagnostics:#?}",
    );
  }
}

#[cfg(feature = "fuzzing")]
mod fuzzing {
  use std::time::{Duration, Instant};

  use serde_json::json;

  struct Lcg(u64);

  impl Lcg {
    fn next_u32(&mut self) -> u32 {
      self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
      (self.0 >> 32) as u32
    }

    fn fill_bytes(&mut self, out: &mut [u8]) {
      let mut idx = 0;
      while idx < out.len() {
        let chunk = self.next_u32().to_le_bytes();
        for b in chunk {
          if idx >= out.len() {
            break;
          }
          out[idx] = b;
          idx += 1;
        }
      }
    }
  }

  #[test]
  #[ignore]
  fn fuzz_smoke_typecheck_pipeline() {
    let mut rng = Lcg(0x1656_67b1_9e37_79f9);
    let start = Instant::now();
    let mut iters = 0usize;

    while iters < 800 && start.elapsed() < Duration::from_secs(3) {
      let len = (rng.next_u32() as usize) % 1024;
      let mut buf = vec![0u8; len];
      rng.fill_bytes(&mut buf);
      typecheck_ts::fuzz::fuzz_typecheck_pipeline(&buf);
      iters += 1;
    }
  }

  #[test]
  #[ignore]
  fn fuzz_smoke_type_graph() {
    let mut rng = Lcg(0x85eb_ca6b_c8f6_9b07);
    let start = Instant::now();
    let mut iters = 0usize;

    while iters < 2_000 && start.elapsed() < Duration::from_secs(3) {
      let node_count = (rng.next_u32() as usize % 16).max(1);
      let mut nodes = Vec::with_capacity(node_count);
      for idx in 0..node_count {
        let kind = rng.next_u32() % 6;
        let node = match kind {
          0 => json!({"kind": "number"}),
          1 => json!({"kind": "string"}),
          2 => json!({"kind": "boolean_literal", "value": (rng.next_u32() & 1) == 1}),
          3 => json!({
            "kind": "array",
            "ty": (rng.next_u32() as usize % node_count),
            "readonly": (rng.next_u32() & 1) == 1
          }),
          4 => json!({
            "kind": "union",
            "members": [(idx + 1) % node_count, (rng.next_u32() as usize % node_count)]
          }),
          _ => json!({
            "kind": "ref",
            "def": (rng.next_u32() % 8) as u32,
            "args": [(rng.next_u32() as usize % node_count)]
          }),
        };
        nodes.push(node);
      }

      let root = (rng.next_u32() as usize) % node_count;
      let graph = json!({
        "roots": [root],
        "nodes": nodes,
      });
      let bytes = serde_json::to_vec(&graph).expect("serialize fuzz graph");
      typecheck_ts::fuzz::fuzz_type_graph(&bytes);
      iters += 1;
    }
  }
}

