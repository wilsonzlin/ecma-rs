use ahash::{HashMap, HashMapExt, HashSet};

pub fn allocate_registers(intgraph: &HashMap<u32, HashSet<u32>>) -> HashMap<u32, u32> {
  let all_colours = HashSet::from_iter(0..u32::try_from(intgraph.len()).unwrap());
  let mut rem = intgraph.clone();
  let mut stack = Vec::new();
  while let Some(t) = rem
    .iter()
    .min_by_key(|(_, c)| c.len())
    .map(|(t, _)| *t)
  {
    stack.push(t);
    let children = rem.remove(&t).unwrap();
    for &c in children.iter() {
      rem.get_mut(&c).unwrap().remove(&t);
    }
  }
  let mut allocated = HashMap::<u32, u32>::new();
  for t in stack.into_iter().rev() {
    let mut avail = all_colours.clone();
    for neighbour in intgraph[&t].iter() {
      if let Some(&neighbour_colour) = allocated.get(&neighbour) {
        avail.remove(&neighbour_colour);
      };
    }
    let pick = *avail.iter().next().unwrap();
    assert!(allocated.insert(t, pick).is_none());
  }
  allocated
}
