// Utility functions demonstrating function composition and higher-order functions
const pipe = (...fns) => x => fns.reduce((v, f) => f(v), x);
const curry = (fn) => (...args) =>
  args.length >= fn.length ? fn(...args) : curry(fn.bind(null, ...args));

// Demonstrating nullish coalescing, optional chaining, and default parameters
const getConfigValue = (obj, path, defaultValue = null) =>
  path.split('.').reduce((acc, part) => acc?.[part] ?? defaultValue, obj);

// Recursive implementation with tail call optimization
const factorial = (n, acc = 1n) =>
  n <= 1n ? acc : factorial(n - 1n, acc * n);

// Duck typing example with Symbol.iterator
const makeIterable = (obj) => ({
  ...obj,
  *[Symbol.iterator]() {
    for (const key in obj) {
      if (Object.prototype.hasOwnProperty.call(obj, key)) {
        yield [key, obj[key]];
      }
    }
  }
});

// Demonstrating various type coercions and operations
const typeCoercionExamples = {
  add: (a, b) => a + b,            // String concatenation vs numeric addition
  subtract: (a, b) => a - b,       // Coercion to number
  toString: () => 1 + "2" + true,  // Mixed type concatenation
  toNumber: () => +"42px",         // String to number coercion
  toBool: () => !!"",              // Double negation to boolean
  equality: () => null == undefined // Loose equality
};

class Task {
  #private = Symbol('private');
  static #instanceCounter = 0;

  constructor({ id = ++Task.#instanceCounter, priority = 0, fn }) {
    this.id = id;
    this.priority = priority;
    this.fn = fn;
    this.status = 'pending';
    this.result = null;
    this.error = null;

    // Circular reference demonstration
    this.self = this;
  }

  // Getter/Setter demonstration
  get isCompleted() {
    return this.status === 'completed';
  }

  set setState(newState) {
    this.status = String(newState).toLowerCase();
  }
}

class PriorityQueue {
  #values = [];

  get isEmpty() {
    return this.#values.length === 0;
  }

  // Demonstrating arrow function properties and this binding
  enqueue = (element, priority) => {
    const queueElement = { element, priority };
    this.#values.push(queueElement);
    this.#bubbleUp();
    return this;
  };

  // Traditional method definition
  dequeue() {
    if (this.isEmpty) return null;

    const [max, ...rest] = this.#values;
    this.#values = rest;

    return max.element;
  }

  // Private method with recursive implementation
  #bubbleUp = (idx = this.#values.length - 1) => {
    if (idx <= 0) return;

    const element = this.#values[idx];
    const parentIdx = Math.floor((idx - 1) / 2);
    const parent = this.#values[parentIdx];

    if (element.priority <= parent.priority) return;

    [this.#values[parentIdx], this.#values[idx]] =
      [this.#values[idx], this.#values[parentIdx]];

    this.#bubbleUp(parentIdx);
  };
}

class TaskScheduler {
  #queue;
  #eventHandlers;
  #running;

  constructor() {
    this.#queue = new PriorityQueue();
    this.#eventHandlers = new Map();
    this.#running = false;

    // Bind event handlers with function composition
    this.handleError = pipe(
      error => ({ timestamp: Date.now(), error }),
      this.#emitEvent.bind(this, 'error')
    );
  }

  // Method demonstrating object destructuring and default parameters
  addTask = ({ fn, priority = 0, id = crypto.randomUUID() } = {}) => {
    if (typeof fn !== 'function') {
      throw new TypeError('Task must be a function');
    }

    const task = new Task({ id, priority, fn });
    this.#queue.enqueue(task, priority);
    this.#emitEvent('taskAdded', { task });

    !this.#running && this.start();

    return task;
  };

  // Async method with try/catch and await
  async start() {
    if (this.#running) return;

    this.#running = true;

    while (this.#running) {
      const task = this.#queue.dequeue();

      if (!task) {
        this.#running = false;
        this.#emitEvent('idle');
        break;
      }

      try {
        task.status = 'running';
        this.#emitEvent('taskStarted', { task });

        // Demonstrate Promise handling
        task.result = await Promise.resolve(task.fn())
          .then(result => (task.status = 'completed', result))
          .catch(error => {
            task.status = 'failed';
            task.error = error;
            throw error;
          });

        this.#emitEvent('taskCompleted', { task });
      } catch (error) {
        this.handleError(error);
      }
    }
  }

  // Event handling with Set operations
  on(event, handler) {
    this.#eventHandlers.set(
      event,
      (this.#eventHandlers.get(event) ?? new Set()).add(handler)
    );
    return () => this.off(event, handler);
  }

  off(event, handler) {
    this.#eventHandlers.get(event)?.delete(handler);
  }

  // Private method demonstrating optional chaining
  #emitEvent(event, data) {
    this.#eventHandlers.get(event)?.forEach(handler => {
      try {
        handler(data);
      } catch (error) {
        console.error(`Error in ${event} handler:`, error);
      }
    });
  }
}

// Example usage demonstrating various features
const scheduler = new TaskScheduler();

// Demonstrating closure and arrow functions
const createCounter = (initial = 0) => {
  let count = initial;
  return () => ++count;
};

// Template literal with embedded expression
const logger = ({ task }) => {
  console.log(`Task ${task.id} ${task.status} at ${new Date().toISOString()}`);
};

// Event subscription with destructuring
scheduler.on('taskCompleted', ({ task: { id, result } }) => {
  console.log(`Result for ${id}:`, result);
});

// Adding tasks with various patterns
scheduler.addTask({
  fn: createCounter(),
  priority: 1
});

scheduler.addTask({
  fn: async () => {
    const result = await Promise.resolve(42);
    return factorial(10n) + BigInt(result);
  },
  priority: 2
});

// Demonstrating error handling and Promises
scheduler.addTask({
  fn: () => Promise.reject(new Error('Intentional failure')),
  priority: 0
});
