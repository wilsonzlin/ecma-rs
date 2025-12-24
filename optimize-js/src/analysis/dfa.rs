use crate::cfg::cfg::Cfg;
use crate::il::inst::Inst;
use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use ahash::HashSetExt;
use itertools::chain;
use itertools::Itertools;
use std::collections::VecDeque;
use std::hash::Hash;

#[derive(Clone, PartialEq, Eq)]
pub enum Set<T: Clone + Eq + Hash> {
  Finite(HashSet<T>),
  Infinite,
}

impl<T: Clone + Eq + Hash> Set<T> {
  pub fn empty() -> Self {
    Set::Finite(HashSet::new())
  }

  pub fn of_one(t: T) -> Self {
    Set::Finite([t].into_iter().collect())
  }

  pub fn union(&self, other: &Self) -> Self {
    match (self, other) {
      (Set::Finite(a), Set::Finite(b)) => Set::Finite(chain!(a, b).cloned().collect()),
      _ => Set::Infinite,
    }
  }

  pub fn intersection(&self, other: &Self) -> Self {
    match (self, other) {
      (Set::Finite(a), Set::Finite(b)) => Set::Finite(a.intersection(b).cloned().collect()),
      (Set::Finite(a), Set::Infinite) => Set::Finite(a.clone()),
      (Set::Infinite, Set::Finite(b)) => Set::Finite(b.clone()),
      (Set::Infinite, Set::Infinite) => Set::Infinite,
    }
  }

  pub fn difference(&self, other: &Self) -> Self {
    match (self, other) {
      (Set::Finite(a), Set::Finite(b)) => Set::Finite(a.difference(b).cloned().collect()),
      (Set::Finite(_), Set::Infinite) => Set::Finite(HashSet::new()),
      (Set::Infinite, Set::Finite(_)) => Set::Finite(HashSet::new()),
      (Set::Infinite, Set::Infinite) => Set::Finite(HashSet::new()),
    }
  }

  pub fn len(&self) -> usize {
    match self {
      Set::Finite(s) => s.len(),
      Set::Infinite => usize::MAX,
    }
  }
}

impl<T: Clone + Eq + Hash> Default for Set<T> {
  fn default() -> Self {
    Set::Finite(HashSet::new())
  }
}

pub trait DataFlowAnalysis<T: Eq, const FORWARDS: bool> {
  // Must be monotonic.
  fn transfer(&mut self, block: &[Inst], in_: &T) -> T;
  fn join(&mut self, pred_outs: &[&T]) -> T;
  fn analyze(&mut self, cfg: &Cfg) {
    let related = |successors: bool, label: u32| {
      if successors || !FORWARDS {
        cfg.graph.children(label)
      } else {
        cfg.graph.parents(label)
      }
    };
    let mut outs = HashMap::<u32, T>::new();
    // TODO u32::MAX does not exist.
    let mut worklist = VecDeque::from([if FORWARDS { 0 } else { u32::MAX }]);
    while let Some(label) = worklist.pop_front() {
      let in_ = self.join(
        &related(false, label)
          .filter_map(|p| outs.get(&p))
          .collect_vec(),
      );
      let out = self.transfer(cfg.bblocks.get(label), &in_);
      let did_change = outs.get(&label).is_none_or(|ex| ex != &out);
      outs.insert(label, out);
      if did_change {
        worklist.extend(related(true, label));
      };
    }
  }
}
