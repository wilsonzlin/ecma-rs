use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use itertools::Itertools;

pub fn calculate_interference_graph(
  liveness: &HashMap<(u32, usize), HashSet<u32>>,
) -> HashMap<u32, HashSet<u32>> {
  // Undirected graph, so two pairs of directed edges for each connection.
  let mut intgraph = HashMap::<u32, HashSet<u32>>::new();
  for lives in liveness.values() {
    let lives = lives.iter().cloned().collect_vec();
    for i in 0..lives.len() {
      // Ensure the node exists in the graph even if no connections.
      intgraph.entry(lives[i]).or_default();
      for j in (i + 1)..lives.len() {
        let (a, b) = (lives[i], lives[j]);
        intgraph.entry(a).or_default().insert(b);
        intgraph.entry(b).or_default().insert(a);
      }
    }
  }
  intgraph
}
