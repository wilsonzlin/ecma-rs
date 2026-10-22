use clap::ValueEnum;
use serde::{Deserialize, Serialize};

/// How to assign cases to shards.
///
/// - [`ShardStrategy::Index`]: partition by position in a deterministically ordered
///   list (callers must sort before applying).
/// - [`ShardStrategy::Hash`]: partition by a stable FNV-1a hash of the case id
///   (order-independent; preferred for CI ratchets when discovery order may drift).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ValueEnum)]
#[serde(rename_all = "snake_case")]
pub enum ShardStrategy {
  Index,
  Hash,
}

/// Deterministic sharding for test case lists.
///
/// For [`ShardStrategy::Index`], sharding is based on the *index in a deterministic
/// ordering* (e.g. sorted by test id), so callers should sort their case list before
/// applying a shard. For [`ShardStrategy::Hash`], use [`Shard::includes_hash`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shard {
  pub index: usize,
  pub total: usize,
}

fn stable_hash64(input: &str) -> u64 {
  const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
  const FNV_PRIME: u64 = 0x100000001b3;

  let mut hash = FNV_OFFSET_BASIS;
  for &byte in input.as_bytes() {
    hash ^= u64::from(byte);
    hash = hash.wrapping_mul(FNV_PRIME);
  }
  hash
}

impl Shard {
  /// Returns whether the shard includes the given 0-based index.
  pub fn includes(&self, idx: usize) -> bool {
    idx % self.total == self.index
  }

  /// Returns whether the shard includes `id` under stable hash partitioning.
  pub fn includes_hash(&self, id: &str) -> bool {
    if self.total == 0 {
      return false;
    }
    (stable_hash64(id) % self.total as u64) as usize == self.index
  }
}

impl std::str::FromStr for Shard {
  type Err = String;

  fn from_str(raw: &str) -> std::result::Result<Self, Self::Err> {
    let Some((index_raw, total_raw)) = raw.split_once('/') else {
      return Err("shard must be in the form <index>/<total>".into());
    };
    let index: usize = index_raw
      .parse()
      .map_err(|err| format!("invalid shard index `{index_raw}`: {err}"))?;
    let total: usize = total_raw
      .parse()
      .map_err(|err| format!("invalid shard total `{total_raw}`: {err}"))?;
    if total == 0 {
      return Err("shard total must be greater than zero".into());
    }
    if index >= total {
      return Err(format!(
        "shard index must be less than total ({} >= {})",
        index, total
      ));
    }

    Ok(Self { index, total })
  }
}

/// Applies a shard to a deterministically-ordered list of items.
pub fn apply_shard<T>(items: impl IntoIterator<Item = T>, shard: Shard) -> Vec<T> {
  items
    .into_iter()
    .enumerate()
    .filter(|(idx, _)| shard.includes(*idx))
    .map(|(_, item)| item)
    .collect()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn shard_parses() {
    let shard: Shard = "0/2".parse().expect("parsed");
    assert_eq!(shard, Shard { index: 0, total: 2 });

    let err = "2/2".parse::<Shard>().unwrap_err();
    assert!(err.contains("index must be less than total"));
  }

  #[test]
  fn sharding_is_deterministic() {
    let cases = vec!["a", "b", "c", "d", "e"];
    let shard = Shard { index: 1, total: 3 };

    let first = apply_shard(cases.clone(), shard);
    let second = apply_shard(cases, shard);

    assert_eq!(first, second);
  }

  #[test]
  fn shards_partition_indices() {
    let items: Vec<_> = (0..20).collect();
    let total = 4;
    let mut seen = vec![0usize; items.len()];

    for index in 0..total {
      let shard = Shard { index, total };
      for item in apply_shard(items.clone(), shard) {
        seen[item] += 1;
      }
    }

    assert!(seen.iter().all(|count| *count == 1));
  }

  #[test]
  fn hash_shards_partition_ids() {
    let ids = ["a/b.ts", "c/d.ts", "e/f.ts", "g/h.ts", "i/j.ts"];
    let total = 3;
    let mut seen = vec![0usize; ids.len()];

    for index in 0..total {
      let shard = Shard { index, total };
      for (i, id) in ids.iter().enumerate() {
        if shard.includes_hash(id) {
          seen[i] += 1;
        }
      }
    }

    assert!(seen.iter().all(|count| *count == 1));
  }

  #[test]
  fn stable_hash64_matches_reference_vectors() {
    assert_eq!(stable_hash64(""), 0xcbf29ce484222325);
    assert_eq!(stable_hash64("a"), 0xaf63dc4c8601ec8c);
    assert_eq!(stable_hash64("foo"), 0xdcb27518fed9d577);
  }

  #[test]
  fn hash_sharding_is_deterministic() {
    let ids = [
      "match/basic.ts",
      "mismatch/type_error.ts",
      "some/dir/file.ts",
    ];
    let total = 8;
    let first: Vec<_> = ids
      .iter()
      .map(|id| (stable_hash64(id) % total as u64) as usize)
      .collect();
    let second: Vec<_> = ids
      .iter()
      .map(|id| (stable_hash64(id) % total as u64) as usize)
      .collect();
    assert_eq!(first, second);
  }
}
