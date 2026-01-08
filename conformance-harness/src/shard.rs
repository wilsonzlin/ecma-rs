/// Deterministic sharding for test case lists.
///
/// Sharding is based on the *index in a deterministic ordering* (e.g. sorted by
/// test id), so callers should sort their case list before applying a shard.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shard {
  pub index: usize,
  pub total: usize,
}

impl Shard {
  /// Returns whether the shard includes the given 0-based index.
  pub fn includes(&self, idx: usize) -> bool {
    idx % self.total == self.index
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
}
