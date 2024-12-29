// Type definitions for improved understanding
/**
 * @typedef {Object} DataNode
 * @property {string} id
 * @property {Set<string>} dependencies
 * @property {Function} transform
 * @property {*} cachedValue
 * @property {number} lastComputed
 * @property {Set<string>} subscribers
 */

/**
 * @typedef {Object} Pipeline
 * @property {string} id
 * @property {DataNode[]} nodes
 * @property {Map<string, *>} values
 * @property {Function} onError
 */

// Utility functions using advanced JS features
const pipe = (...fns) => x => fns.reduce((v, f) => f(v), x);
const curry = fn => (...args) =>
  args.length >= fn.length ? fn(...args) : curry(fn.bind(null, ...args));

// WeakMap for private state
const nodeStates = new WeakMap();
const pipelineStates = new WeakMap();

// Symbol for internal methods
const internal = {
  compute: Symbol('compute'),
  validate: Symbol('validate'),
  notify: Symbol('notify'),
  cleanup: Symbol('cleanup')
};

// Advanced cache implementation with LRU and weak references
class Cache {
  #maxSize;
  #values = new Map();
  #usage = new Map();
  #refs = new WeakMap();

  constructor(maxSize = 1000) {
    this.#maxSize = maxSize;
  }

  set(key, value) {
    if (this.#values.size >= this.#maxSize) {
      // Find least recently used
      let minUsage = Infinity;
      let lruKey;
      for (const [k, usage] of this.#usage) {
        if (usage < minUsage) {
          minUsage = usage;
          lruKey = k;
        }
      }
      this.delete(lruKey);
    }

    this.#values.set(key, value);
    this.#usage.set(key, Date.now());

    if (typeof value === 'object' && value !== null) {
      this.#refs.set(value, key);
    }

    return this;
  }

  get(key) {
    if (this.#values.has(key)) {
      this.#usage.set(key, Date.now());
      return this.#values.get(key);
    }
    return undefined;
  }

  delete(key) {
    const value = this.#values.get(key);
    this.#values.delete(key);
    this.#usage.delete(key);
    if (value && typeof value === 'object') {
      this.#refs.delete(value);
    }
  }

  clear() {
    this.#values.clear();
    this.#usage.clear();
    this.#refs = new WeakMap();
  }
}

// Reactive data node implementation
class DataNode {
  #state;
  #pipeline;
  #cache;

  constructor(id, options = {}) {
    const {
      transform = x => x,
      dependencies = new Set(),
      cache = new Cache(100)
    } = options;

    this.id = id;
    this.#cache = cache;
    this.#state = {
      transform,
      dependencies,
      subscribers: new Set(),
      lastComputed: 0,
      computing: false
    };

    nodeStates.set(this, this.#state);
  }

  async [internal.compute](pipeline, force = false) {
    const state = this.#state;

    if (state.computing) {
      throw new Error(`Circular computation detected in node ${this.id}`);
    }

    const deps = Array.from(state.dependencies);
    const cacheKey = deps.map(d => pipeline.values.get(d)).join('|');

    if (!force && this.#cache.has(cacheKey)) {
      return this.#cache.get(cacheKey);
    }

    state.computing = true;
    try {
      const depValues = await Promise.all(
        deps.map(async d => {
          const node = pipeline.getNode(d);
          if (!node) throw new Error(`Dependency ${d} not found`);
          return node[internal.compute](pipeline);
        })
      );

      const result = await Promise.resolve(
        state.transform(...depValues)
      );

      this.#cache.set(cacheKey, result);
      state.lastComputed = Date.now();

      return result;
    } finally {
      state.computing = false;
    }
  }

  subscribe(nodeId) {
    this.#state.subscribers.add(nodeId);
    return () => this.#state.subscribers.delete(nodeId);
  }

  dependsOn(nodeId) {
    this.#state.dependencies.add(nodeId);
    return this;
  }

  transform(fn) {
    this.#state.transform = fn;
    return this;
  }
}

// Pipeline implementation for managing data flow
class Pipeline {
  #nodes = new Map();
  #values = new Map();
  #state;

  constructor(id, options = {}) {
    this.id = id;
    this.#state = {
      status: 'idle',
      error: null,
      onError: options.onError ?? console.error
    };

    pipelineStates.set(this, this.#state);
  }

  addNode(nodeId, options = {}) {
    if (this.#nodes.has(nodeId)) {
      throw new Error(`Node ${nodeId} already exists`);
    }

    const node = new DataNode(nodeId, options);
    this.#nodes.set(nodeId, node);
    return node;
  }

  getNode(nodeId) {
    return this.#nodes.get(nodeId);
  }

  async setValue(nodeId, value) {
    this.#values.set(nodeId, value);

    // Update dependent nodes
    const affected = new Set([nodeId]);
    const visited = new Set();

    for (const [id, node] of this.#nodes) {
      const state = nodeStates.get(node);
      if (state.dependencies.has(nodeId)) {
        affected.add(id);
      }
    }

    for (const id of affected) {
      if (visited.has(id)) continue;
      visited.add(id);

      const node = this.#nodes.get(id);
      if (!node) continue;

      try {
        const result = await node[internal.compute](this, true);
        this.#values.set(id, result);

        // Notify subscribers
        const state = nodeStates.get(node);
        for (const subId of state.subscribers) {
          affected.add(subId);
        }
      } catch (error) {
        this.#state.error = error;
        this.#state.onError(error);
      }
    }
  }

  async getValue(nodeId) {
    const node = this.#nodes.get(nodeId);
    if (!node) {
      throw new Error(`Node ${nodeId} not found`);
    }

    if (!this.#values.has(nodeId)) {
      const result = await node[internal.compute](this);
      this.#values.set(nodeId, result);
    }

    return this.#values.get(nodeId);
  }

  // Pipeline composition
  compose(other) {
    const composed = new Pipeline(`${this.id}_${other.id}`);

    // Copy nodes from both pipelines
    for (const [id, node] of this.#nodes) {
      composed.#nodes.set(id, node);
    }
    for (const [id, node] of other.#nodes) {
      if (composed.#nodes.has(id)) {
        throw new Error(`Node ${id} already exists in composed pipeline`);
      }
      composed.#nodes.set(id, node);
    }

    return composed;
  }
}

// Example usage demonstrating complex features
async function example() {
  // Create a pipeline for data processing
  const pipeline = new Pipeline('main', {
    onError: error => console.error('Pipeline error:', error)
  });

  // Add data source nodes
  pipeline.addNode('source1');
  pipeline.addNode('source2');

  // Add transformation nodes with dependencies
  pipeline.addNode('combined', {
    transform: (s1, s2) => ({ ...s1, ...s2 })
  }).dependsOn('source1').dependsOn('source2');

  pipeline.addNode('processed', {
    transform: combined => {
      const { x = 0, y = 0, z = 0 } = combined;
      return Math.sqrt(x * x + y * y + z * z);
    }
  }).dependsOn('combined');

  // Add nodes with async transformations
  pipeline.addNode('async1', {
    transform: async value => {
      await new Promise(resolve => setTimeout(resolve, 100));
      return value * 2;
    }
  }).dependsOn('processed');

  pipeline.addNode('async2', {
    transform: async value => {
      await new Promise(resolve => setTimeout(resolve, 50));
      return value + 1;
    }
  }).dependsOn('async1');

  // Set up subscriptions
  const processed = pipeline.getNode('processed');
  const async1 = pipeline.getNode('async1');
  const async2 = pipeline.getNode('async2');

  processed.subscribe('async1');
  async1.subscribe('async2');

  // Update values and observe propagation
  await pipeline.setValue('source1', { x: 3, y: 4 });
  await pipeline.setValue('source2', { z: 5 });

  // Get computed results
  console.log('Processed:', await pipeline.getValue('processed'));
  console.log('Async1:', await pipeline.getValue('async1'));
  console.log('Async2:', await pipeline.getValue('async2'));

  // Compose with another pipeline
  const other = new Pipeline('secondary');
  other.addNode('source3');
  other.addNode('derived', {
    transform: value => value * 3
  }).dependsOn('source3');

  const composed = pipeline.compose(other);
  await composed.setValue('source3', 10);
  console.log('Derived:', await composed.getValue('derived'));
}

// Run the example
example().catch(console.error);
