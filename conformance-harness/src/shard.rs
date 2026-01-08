#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Shard {
  pub index: usize,
  pub total: usize,
}

impl Shard {
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
