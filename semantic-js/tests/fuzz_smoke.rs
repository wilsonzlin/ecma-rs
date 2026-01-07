#![cfg(feature = "fuzzing")]

use std::time::{Duration, Instant};

struct Lcg(u64);

impl Lcg {
  fn next_u32(&mut self) -> u32 {
    // PCG-style LCG constants.
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
fn fuzz_smoke_js_binder() {
  let mut rng = Lcg(0x9e37_79b9_7f4a_7c15);
  let start = Instant::now();
  let mut iters = 0usize;

  while iters < 5_000 && start.elapsed() < Duration::from_secs(2) {
    let len = (rng.next_u32() as usize) % 512;
    let mut buf = vec![0u8; len];
    rng.fill_bytes(&mut buf);

    semantic_js::fuzz::fuzz_js_binder(&buf);
    iters += 1;
  }
}

#[test]
#[ignore]
fn fuzz_smoke_ts_binder() {
  let mut rng = Lcg(0x243f_6a88_85a3_08d3);
  let start = Instant::now();
  let mut iters = 0usize;

  while iters < 5_000 && start.elapsed() < Duration::from_secs(2) {
    let len = (rng.next_u32() as usize) % 512;
    let mut buf = vec![0u8; len];
    rng.fill_bytes(&mut buf);

    semantic_js::fuzz::fuzz_ts_binder(&buf);
    iters += 1;
  }
}
