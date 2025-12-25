use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;

pub fn allocate_registers(intgraph: &HashMap<u32, HashSet<u32>>) -> HashMap<u32, u32> {
  let mut rem = intgraph.clone();
  let mut stack = Vec::new();
  while let Some(t) = rem
    .iter()
    .min_by(|(t1, c1), (t2, c2)| c1.len().cmp(&c2.len()).then_with(|| t1.cmp(t2)))
    .map(|(t, _)| *t)
  {
    stack.push(t);
    let children = rem.remove(&t).unwrap();
    for &c in children.iter() {
      rem.get_mut(&c).unwrap().remove(&t);
    }
  }
  let mut allocated = HashMap::<u32, u32>::new();
  let max_colour = u32::try_from(intgraph.len()).unwrap();
  for t in stack.into_iter().rev() {
    let mut used = HashSet::default();
    for neighbour in intgraph[&t].iter() {
      if let Some(&neighbour_colour) = allocated.get(&neighbour) {
        used.insert(neighbour_colour);
      };
    }
    let pick = (0..max_colour).find(|c| !used.contains(c)).unwrap();
    assert!(allocated.insert(t, pick).is_none());
  }
  allocated
}

#[cfg(test)]
mod tests {
  use super::allocate_registers;
  use ahash::{HashMap, HashMapExt, HashSet};

  #[test]
  fn empty_graph_allocates_no_registers() {
    let intgraph: HashMap<u32, HashSet<u32>> = HashMap::new();
    let allocated = allocate_registers(&intgraph);
    assert!(allocated.is_empty());
  }
}
