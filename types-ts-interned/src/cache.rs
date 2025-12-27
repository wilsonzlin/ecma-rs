use parking_lot::Mutex;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash, Hasher};

type StableHasher = ahash::RandomState;

fn stable_hasher() -> StableHasher {
  ahash::RandomState::with_seeds(0, 0, 0, 0)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CacheConfig {
  pub max_entries: usize,
  pub shard_count: usize,
}

impl CacheConfig {
  pub fn disabled() -> Self {
    Self {
      max_entries: 0,
      shard_count: 1,
    }
  }

  fn normalize(self) -> Self {
    Self {
      max_entries: self.max_entries,
      shard_count: self.shard_count.max(1),
    }
  }
}

impl Default for CacheConfig {
  fn default() -> Self {
    Self {
      max_entries: 4096,
      shard_count: 8,
    }
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CacheStats {
  pub hits: u64,
  pub misses: u64,
  pub insertions: u64,
  pub evictions: u64,
}

impl CacheStats {
  pub fn merge(&mut self, other: &CacheStats) {
    self.hits += other.hits;
    self.misses += other.misses;
    self.insertions += other.insertions;
    self.evictions += other.evictions;
  }
}

#[derive(Debug)]
struct ClockEntry<K, V> {
  key: K,
  value: V,
  ref_bit: bool,
}

#[derive(Debug)]
struct ClockCache<K, V> {
  entries: Vec<ClockEntry<K, V>>,
  index: HashMap<K, usize, StableHasher>,
  hand: usize,
  capacity: usize,
  stats: CacheStats,
}

impl<K: Eq + Hash + Clone, V: Clone> ClockCache<K, V> {
  fn new(capacity: usize) -> Self {
    Self {
      entries: Vec::new(),
      index: HashMap::with_hasher(stable_hasher()),
      hand: 0,
      capacity,
      stats: CacheStats::default(),
    }
  }

  fn len(&self) -> usize {
    self.entries.len()
  }

  fn contains(&self, key: &K) -> bool {
    self.index.contains_key(key)
  }

  fn stats(&self) -> CacheStats {
    self.stats
  }

  fn get(&mut self, key: &K) -> Option<V> {
    if self.capacity == 0 {
      self.stats.misses += 1;
      return None;
    }
    match self.index.get(key).copied() {
      Some(idx) => {
        self.stats.hits += 1;
        if let Some(entry) = self.entries.get_mut(idx) {
          entry.ref_bit = true;
          return Some(entry.value.clone());
        }
        None
      }
      None => {
        self.stats.misses += 1;
        None
      }
    }
  }

  fn remove(&mut self, key: &K) -> Option<V> {
    let idx = self.index.remove(key)?;
    let entry = self.entries.swap_remove(idx);
    if idx < self.entries.len() {
      let swapped_key = self.entries[idx].key.clone();
      self.index.insert(swapped_key, idx);
    }
    if self.hand > idx && self.hand != 0 {
      self.hand -= 1;
    }
    if self.hand >= self.entries.len() {
      self.hand = 0;
    }
    Some(entry.value)
  }

  fn insert(&mut self, key: K, value: V) {
    if self.capacity == 0 {
      return;
    }
    self.stats.insertions += 1;
    if let Some(idx) = self.index.get(&key).copied() {
      if let Some(entry) = self.entries.get_mut(idx) {
        entry.value = value;
        entry.ref_bit = true;
      }
      return;
    }

    if self.entries.len() >= self.capacity {
      self.evict_one();
    }

    let idx = self.entries.len();
    self.entries.push(ClockEntry {
      key: key.clone(),
      value,
      ref_bit: true,
    });
    self.index.insert(key, idx);
  }

  fn evict_one(&mut self) {
    if self.entries.is_empty() {
      return;
    }
    loop {
      if self.hand >= self.entries.len() {
        self.hand = 0;
      }
      if let Some(entry) = self.entries.get_mut(self.hand) {
        if entry.ref_bit {
          entry.ref_bit = false;
          self.hand += 1;
          continue;
        }
      }

      let evicted_idx = self.hand;
      let evicted_key = self.entries[evicted_idx].key.clone();
      self.stats.evictions += 1;
      let last_idx = self.entries.len() - 1;
      self.entries.swap(evicted_idx, last_idx);
      self.entries.pop();
      self.index.remove(&evicted_key);
      if evicted_idx < self.entries.len() {
        let swapped_key = self.entries[evicted_idx].key.clone();
        self.index.insert(swapped_key, evicted_idx);
      }
      if self.hand >= self.entries.len() {
        self.hand = 0;
      }
      break;
    }
  }

  fn clear(&mut self) {
    self.entries.clear();
    self.index.clear();
    self.hand = 0;
    self.stats = CacheStats::default();
  }

  fn entries(&self) -> Vec<(K, V)> {
    self
      .entries
      .iter()
      .map(|entry| (entry.key.clone(), entry.value.clone()))
      .collect()
  }
}

#[derive(Debug)]
pub struct ShardedCache<K, V> {
  shards: Vec<Mutex<ClockCache<K, V>>>,
}

impl<K: Eq + Hash + Clone, V: Clone> ShardedCache<K, V> {
  pub fn new(config: CacheConfig) -> Self {
    let config = config.normalize();
    let mut shards = Vec::with_capacity(config.shard_count);
    let base = config.max_entries / config.shard_count;
    let remainder = config.max_entries % config.shard_count;
    for idx in 0..config.shard_count {
      let capacity = base + usize::from(idx < remainder);
      shards.push(Mutex::new(ClockCache::new(capacity)));
    }
    Self { shards }
  }

  pub fn len(&self) -> usize {
    self.shards.iter().map(|shard| shard.lock().len()).sum()
  }

  pub fn stats(&self) -> CacheStats {
    let mut stats = CacheStats::default();
    for shard in &self.shards {
      stats.merge(&shard.lock().stats());
    }
    stats
  }

  pub fn get(&self, key: &K) -> Option<V> {
    let idx = self.shard_index(key);
    self.shards[idx].lock().get(key)
  }

  pub fn contains(&self, key: &K) -> bool {
    let idx = self.shard_index(key);
    self.shards[idx].lock().contains(key)
  }

  pub fn insert(&self, key: K, value: V) {
    let idx = self.shard_index(&key);
    self.shards[idx].lock().insert(key, value);
  }

  pub fn remove(&self, key: &K) -> Option<V> {
    let idx = self.shard_index(key);
    self.shards[idx].lock().remove(key)
  }

  pub fn entries(&self) -> Vec<(K, V)> {
    self
      .shards
      .iter()
      .flat_map(|shard| shard.lock().entries())
      .collect()
  }

  pub fn clear(&self) {
    for shard in &self.shards {
      shard.lock().clear();
    }
  }

  fn shard_index(&self, key: &K) -> usize {
    if self.shards.len() == 1 {
      return 0;
    }
    let mut hasher = stable_hasher().build_hasher();
    key.hash(&mut hasher);
    (hasher.finish() as usize) % self.shards.len()
  }
}
