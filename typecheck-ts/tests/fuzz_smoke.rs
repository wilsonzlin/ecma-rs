#![cfg(feature = "fuzzing")]

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
        3 => {
          json!({"kind": "array", "ty": (rng.next_u32() as usize % node_count), "readonly": (rng.next_u32() & 1) == 1})
        }
        4 => {
          json!({"kind": "union", "members": [(idx + 1) % node_count, (rng.next_u32() as usize % node_count)]})
        }
        _ => {
          json!({"kind": "ref", "def": (rng.next_u32() % 8) as u32, "args": [(rng.next_u32() as usize % node_count)]})
        }
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
