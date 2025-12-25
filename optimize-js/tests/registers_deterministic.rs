use ahash::HashMap;
use ahash::HashSet;
use ahash::RandomState;
use optimize_js::analysis::registers::allocate_registers;

fn add_edge(graph: &mut HashMap<u32, HashSet<u32>>, a: u32, b: u32) {
  graph.get_mut(&a).unwrap().insert(b);
  graph.get_mut(&b).unwrap().insert(a);
}

fn build_graph(state: RandomState) -> HashMap<u32, HashSet<u32>> {
  let mut graph: HashMap<u32, HashSet<u32>> = HashMap::with_hasher(state.clone());
  for node in [0, 1, 2, 3] {
    graph.insert(node, HashSet::with_hasher(state.clone()));
  }

  add_edge(&mut graph, 0, 1);
  add_edge(&mut graph, 0, 2);
  add_edge(&mut graph, 1, 2);
  add_edge(&mut graph, 2, 3);

  graph
}

#[test]
fn allocate_registers_is_deterministic() {
  let expected_mapping: HashMap<u32, u32> = [(0, 2), (1, 1), (2, 0), (3, 1)].into_iter().collect();

  let seeds = [
    RandomState::with_seeds(1, 2, 3, 4),
    RandomState::with_seeds(5, 6, 7, 8),
    RandomState::with_seeds(9, 10, 11, 12),
  ];

  for state in seeds {
    let graph = build_graph(state);
    let result = allocate_registers(&graph);
    assert_eq!(result, expected_mapping);

    for _ in 0..5 {
      assert_eq!(allocate_registers(&graph), expected_mapping);
    }
  }
}
