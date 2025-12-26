use std::hash::{Hash, Hasher};

/// Simple, deterministic 64-bit FNV-1a hasher for content-addressed IDs.
struct StableHasher(u64);

impl StableHasher {
  const OFFSET: u64 = 0xcbf29ce484222325;
  const PRIME: u64 = 0x100000001b3;

  fn new() -> Self {
    StableHasher(Self::OFFSET)
  }
}

impl Hasher for StableHasher {
  fn finish(&self) -> u64 {
    self.0
  }

  fn write(&mut self, bytes: &[u8]) {
    for b in bytes {
      self.0 ^= *b as u64;
      self.0 = self.0.wrapping_mul(Self::PRIME);
    }
  }
}

/// Computes a stable 64-bit hash for any `Hash`able value.
pub(crate) fn stable_hash<T: Hash>(value: &T) -> u64 {
  let mut hasher = StableHasher::new();
  value.hash(&mut hasher);
  hasher.finish()
}

/// Computes a stable 32-bit hash by folding the 64-bit FNV-1a output. This is
/// useful for content-addressed IDs that need to fit into `u32` slots.
pub(crate) fn stable_hash_u32<T: Hash>(value: &T) -> u32 {
  let hash = stable_hash(value);
  (hash ^ (hash >> 32)) as u32
}
