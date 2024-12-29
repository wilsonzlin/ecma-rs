// Types that challenge static analysis
const META = Symbol('meta');
const QUEUE = Symbol('queue');

class StreamValue {
  constructor(value, meta = {}) {
    this.value = value;
    this[META] = meta;

    return new Proxy(this, {
      get(target, prop) {
        if (prop in target) return target[prop];
        if (typeof target.value?.[prop] === 'function') {
          return (...args) => new StreamValue(
            target.value[prop](...args),
            target[META]
          );
        }
        return new StreamValue(target.value?.[prop], target[META]);
      }
    });
  }

  // Force type coercion through valueOf/toString
  valueOf() {
    return this.value?.valueOf?.() ?? this.value;
  }

  toString() {
    return String(this.valueOf());
  }

  // Type conversion methods that preserve metadata
  [Symbol.toPrimitive](hint) {
    const value = this.value;
    if (hint === 'number') return Number(value);
    if (hint === 'string') return String(value);
    return value?.valueOf?.() ?? value;
  }
}

// Stream operators with complex type interactions
const operators = {
  map: fn => stream => stream.pipe(async function*(source) {
    for await (const chunk of source) {
      yield new StreamValue(
        await fn(chunk),
        chunk[META]
      );
    }
  }),

  filter: predicate => stream => stream.pipe(async function*(source) {
    for await (const chunk of source) {
      if (await predicate(chunk)) {
        yield chunk;
      }
    }
  }),

  reduce: (fn, initial) => stream => stream.pipe(async function*(source) {
    let acc = initial;
    for await (const chunk of source) {
      acc = await fn(acc, chunk);
    }
    yield new StreamValue(acc);
  }),

  flatten: () => stream => stream.pipe(async function*(source) {
    for await (const chunk of source) {
      const value = chunk.value;
      if (Symbol.iterator in Object(value)) {
        for (const item of value) {
          yield new StreamValue(item, chunk[META]);
        }
      } else if (Symbol.asyncIterator in Object(value)) {
        for await (const item of value) {
          yield new StreamValue(item, chunk[META]);
        }
      } else {
        yield chunk;
      }
    }
  }),

  batch: size => stream => stream.pipe(async function*(source) {
    let batch = [];
    for await (const chunk of source) {
      batch.push(chunk);
      if (batch.length >= size) {
        yield new StreamValue(batch);
        batch = [];
      }
    }
    if (batch.length > 0) {
      yield new StreamValue(batch);
    }
  }),

  debounce: ms => stream => stream.pipe(async function*(source) {
    let timeout;
    let lastValue;

    const flush = () => new Promise(resolve => {
      if (timeout) clearTimeout(timeout);
      timeout = setTimeout(resolve, ms);
    });

    for await (const chunk of source) {
      lastValue = chunk;
      await flush();
    }

    if (lastValue !== undefined) {
      yield lastValue;
    }
  }),

  distinct: (keyFn = x => x) => stream => stream.pipe(async function*(source) {
    const seen = new WeakSet();
    const seenPrimitives = new Set();

    for await (const chunk of source) {
      const key = await keyFn(chunk);
      const primitive = Object(key) !== key;

      if (primitive) {
        if (!seenPrimitives.has(key)) {
          seenPrimitives.add(key);
          yield chunk;
        }
      } else if (!seen.has(key)) {
        seen.add(key);
        yield chunk;
      }
    }
  })
};

// Main stream processing class
class Stream {
  #transforms = [];
  #source;
  #errorHandler = console.error;

  constructor(source) {
    this.#source = source;
    // Internal queue for buffering
    this[QUEUE] = [];
  }

  // Compose transforms using generator delegation
  pipe(transform) {
    this.#transforms.push(transform);
    return this;
  }

  // Add operators to prototype dynamically
  static {
    Object.entries(operators).forEach(([name, operator]) => {
      Stream.prototype[name] = function(...args) {
        return operator(...args)(this);
      };
    });
  }

  // Async iterator implementation
  async *[Symbol.asyncIterator]() {
    let source = this.#source;

    // Apply transforms sequentially
    for (const transform of this.#transforms) {
      source = transform(source);
    }

    try {
      for await (const chunk of source) {
        yield chunk;
      }
    } catch (error) {
      this.#errorHandler(error);
    }
  }

  // Convenience methods for consumption
  async collect() {
    const results = [];
    for await (const chunk of this) {
      results.push(chunk);
    }
    return results;
  }

  async forEach(fn) {
    for await (const chunk of this) {
      await fn(chunk);
    }
  }

  async consume() {
    for await (const _ of this) {
      // Consume without storing
    }
  }
}

// Example usage with complex type interactions
async function example() {
  // Create source stream with mixed types
  const source = new Stream((async function*() {
    yield new StreamValue(1);
    yield new StreamValue("2");
    yield new StreamValue([3, 4, 5]);
    yield new StreamValue({ value: 6 });
    yield new StreamValue(null);
    yield new StreamValue(undefined);
    yield new StreamValue(Symbol('test'));
    yield new StreamValue(42n);
  })());

  // Complex transformation pipeline
  const results = await source
    .map(x => x.value)
    .filter(x => x != null)
    .map(x => Array.isArray(x) ? x : [x])
    .flatten()
    .map(x => +x || 0)
    .batch(2)
    .map(batch => batch.reduce((a, b) => a + b, 0))
    .distinct()
    .collect();

  console.log('Results:', results);

  // Stream with async transformations and error handling
  const asyncStream = new Stream((async function*() {
    for (let i = 0; i < 5; i++) {
      yield new StreamValue(
        new Promise(resolve =>
          setTimeout(() => resolve(i), Math.random() * 1000)
        )
      );
    }
  })());

  // Process async values with debouncing
  const asyncResults = await asyncStream
    .map(async x => {
      const value = await x;
      if (value % 2 === 0) throw new Error(`Even number: ${value}`);
      return value;
    })
    .filter(x => x > 1)
    .debounce(500)
    .collect();

  console.log('Async results:', asyncResults);
}

// Run example
example().catch(console.error);
