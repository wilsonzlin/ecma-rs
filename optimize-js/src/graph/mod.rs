use ahash::HashMap;
use ahash::HashMapExt;
use ahash::HashSet;
use ahash::HashSetExt;
use std::collections::hash_set;
use std::hash::Hash;
use std::iter;
use std::option;

struct PostOrderVisitor<'a, K: Clone + Default + Eq + Hash + Ord> {
  graph: &'a Graph<K>,
  seen: HashSet<&'a K>,
  order: Vec<&'a K>,
  // Consider parents as successors and children as predecessors i.e. reverse graph edges.
  // NOTE: Not the same as reverse postorder.
  reversed_graph: bool,
}

impl<'a, K: Clone + Default + Eq + Hash + Ord> PostOrderVisitor<'a, K> {
  fn visit(&mut self, n: &'a K) {
    if self.seen.contains(n) {
      return;
    };
    self.seen.insert(n);
    let mut children: Vec<&K> = if self.reversed_graph {
      self.graph.parents(n)
    } else {
      self.graph.children(n)
    }
    .collect();
    children.sort_unstable();
    for c in children {
      self.visit(c);
    }
    self.order.push(n);
  }
}

#[derive(Clone, Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
struct GraphNode<K: Clone + Default + Hash + Eq> {
  children: HashSet<K>,
  parents: HashSet<K>,
}

/// General implementation of a directed graph, implemented separately and generically for robustness.
/// Holds mapped data so that data conveniently remains in sync with graph operations.
/// All operations must be correct for:
/// - Self edges
/// - Cycles
/// - Empty graphs
/// - Disconnected components
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Graph<K: Clone + Default + Hash + Eq> {
  nodes: HashMap<K, GraphNode<K>>,
}

// This is a concrete type instead of `impl Iterator<Item=&K>` so that parents() and children() have the same return type and can be used as such (e.g. both branches of an if-else).
pub type GraphRelatedNodesIter<'a, K> = iter::Flatten<option::IntoIter<hash_set::Iter<'a, K>>>;

impl<K: Clone + Default + Hash + Eq> Graph<K> {
  pub fn new() -> Self {
    Graph {
      nodes: HashMap::new(),
    }
  }

  pub fn contains(&self, node: &K) -> bool {
    self.nodes.contains_key(node)
  }

  pub fn nodes(&self) -> impl Iterator<Item = &K> + '_ {
    self.nodes.keys()
  }

  pub fn edges<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a K)> + 'a {
    self
      .nodes
      .iter()
      .flat_map(|(parent, node)| node.children.iter().map(move |child| (parent, child)))
  }

  pub fn parents(&self, node: &K) -> GraphRelatedNodesIter<'_, K> {
    self
      .nodes
      .get(node)
      .map(|node| node.parents.iter())
      .into_iter()
      .flatten()
  }

  /// Will never contain duplicates as we use a set internally.
  pub fn children(&self, node: &K) -> GraphRelatedNodesIter<'_, K> {
    self
      .nodes
      .get(node)
      .map(|node| node.children.iter())
      .into_iter()
      .flatten()
  }

  /// Insert the nodes and connect them with an edge.
  /// It's safe if the edge already exists.
  pub fn connect(&mut self, parent: &K, child: &K) {
    self
      .nodes
      .entry(parent.clone())
      .or_default()
      .children
      .insert(child.clone());
    self
      .nodes
      .entry(child.clone())
      .or_default()
      .parents
      .insert(parent.clone());
  }

  /// The nodes must already exist.
  /// It's safe if the edge doesn't exist.
  pub fn disconnect(&mut self, parent: &K, child: &K) {
    self.nodes.get_mut(parent).unwrap().children.remove(child);
    self.nodes.get_mut(child).unwrap().parents.remove(parent);
  }

  /// Remove a disconnected node from the graph.
  /// Panics if still connected or doesn't exist.
  pub fn pop(&mut self, node: &K) {
    let r = self.nodes.remove(node).unwrap();
    assert!(r.parents.is_empty());
    assert!(r.children.is_empty());
  }

  /// Remove a node from the graph, connecting all its parents to all its children.
  pub fn contract(&mut self, node: &K) {
    let GraphNode {
      mut children,
      mut parents,
    } = self.nodes.remove(node).unwrap();
    // All of the following graph operations will fail if there's a self-edge since we've just removed it from the graph,
    // so remove any self-edge now.
    children.remove(node);
    parents.remove(node);

    for parent in &parents {
      self
        .nodes
        .get_mut(&parent)
        .unwrap()
        .children
        .extend(children.iter().cloned());
    }

    for child in &children {
      self
        .nodes
        .get_mut(&child)
        .unwrap()
        .parents
        .extend(parents.iter().cloned());
    }

    for parent in parents {
      self.nodes.get_mut(&parent).unwrap().children.remove(node);
    }

    for child in children {
      self.nodes.get_mut(&child).unwrap().parents.remove(node);
    }
  }

  fn _calculate_postorder<'a>(
    &'a self,
    entry: &'a K,
    reversed_graph: bool,
  ) -> (Vec<&'a K>, HashMap<&'a K, usize>)
  where
    K: Ord,
  {
    let mut order_po_v = PostOrderVisitor {
      graph: self,
      order: Vec::new(),
      seen: HashSet::new(),
      reversed_graph,
    };
    order_po_v.visit(entry);
    // Order of nodes to visit in order to visit by postorder. This can also be used to map from postorder number (i.e. number each node would be assigned if sequentially visited and assigned in postorder) to node.
    let po = order_po_v.order;
    // Map from postorder number to node (see above).
    let node_to_po = po
      .iter()
      .enumerate()
      .map(|(i, l)| (*l, i))
      .collect::<HashMap<_, _>>();
    (po, node_to_po)
  }

  /// Postorder: visit all children, then self.
  pub fn calculate_postorder<'a>(&'a self, entry: &'a K) -> (Vec<&'a K>, HashMap<&'a K, usize>)
  where
    K: Ord,
  {
    self._calculate_postorder(entry, false)
  }

  /// Calculate postorder on the reversed graph (graph where children are parents and parents are children i.e. edges reversed).
  /// WARNING: This is not the same as the reverse postorder.
  pub fn calculate_reversed_graph_postorder<'a>(
    &'a self,
    entry: &'a K,
  ) -> (Vec<&'a K>, HashMap<&'a K, usize>)
  where
    K: Ord,
  {
    self._calculate_postorder(entry, true)
  }
}

#[cfg(test)]
mod tests {
  use super::Graph;
  use ahash::HashSet;

  fn assert_edges(graph: &Graph<u32>, edges: &[(u32, u32)]) {
    assert_eq!(
      graph
        .edges()
        .map(|(parent, child)| (parent.clone(), child.clone()))
        .collect::<HashSet<_>>(),
      HashSet::from_iter(edges.into_iter().cloned())
    );
  }

  #[test]
  fn test_contract_with_self_edge_and_no_parents_and_no_children() {
    let mut graph = Graph::<u32>::new();
    graph.connect(&1, &1);
    graph.connect(&2, &3);
    graph.connect(&2, &4);
    graph.connect(&3, &3);
    graph.connect(&3, &4);
    graph.connect(&3, &5);
    graph.contract(&1);
    assert_edges(&graph, &[(2, 3), (2, 4), (3, 3), (3, 4), (3, 5)]);
  }

  #[test]
  fn test_contract_with_self_edge_and_parents_and_no_children() {
    let mut graph = Graph::<u32>::new();
    graph.connect(&1, &1);
    graph.connect(&2, &1);
    graph.connect(&2, &3);
    graph.connect(&2, &4);
    graph.connect(&3, &3);
    graph.connect(&3, &4);
    graph.connect(&3, &5);
    graph.connect(&5, &1);
    graph.contract(&1);
    assert_edges(&graph, &[(2, 3), (2, 4), (3, 3), (3, 4), (3, 5)]);
  }

  #[test]
  fn test_contract_with_self_edge_and_no_parents_and_children() {
    let mut graph = Graph::<u32>::new();
    graph.connect(&1, &1);
    graph.connect(&1, &3);
    graph.connect(&2, &3);
    graph.connect(&2, &4);
    graph.connect(&3, &3);
    graph.connect(&3, &4);
    graph.connect(&3, &5);
    graph.contract(&1);
    assert_edges(&graph, &[(2, 3), (2, 4), (3, 3), (3, 4), (3, 5)]);
  }

  #[test]
  fn test_contract_with_self_edge_and_parents_and_children() {
    let mut graph = Graph::<u32>::new();
    graph.connect(&1, &1);
    graph.connect(&1, &3);
    graph.connect(&2, &1);
    graph.connect(&2, &3);
    graph.connect(&2, &4);
    graph.connect(&3, &3);
    graph.connect(&3, &4);
    graph.connect(&3, &5);
    graph.connect(&5, &1);
    graph.contract(&1);
    assert_edges(&graph, &[(2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (5, 3)]);
  }
}
