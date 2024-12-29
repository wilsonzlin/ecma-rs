// Highly polymorphic function with complex type interactions
const polymorph = (x) => {
  // Type branching based on runtime checks
  if (typeof x === 'number') {
    return x === 0 ? false : !!x;
  }
  if (x?.constructor === String) {
    return x.length > 2 ? x : +x || x;
  }
  return x == null ? undefined
    : Array.isArray(x) ? x.map(polymorph)
    : Object(x) === x ? Object.fromEntries(
        Object.entries(x).map(([k, v]) => [
          k + (typeof v === 'symbol' ? Symbol() : ''),
          polymorph(v)
        ])
      )
    : String(x);
};

// Complex union type behavior through object shapes
const shapeShifter = {
  value: 1,
  get next() {
    this.value = {
      toString() { return 2; },
      valueOf() { return 3; },
      [Symbol.toPrimitive](hint) {
        this.value = hint === 'number' ? '4'
          : hint === 'string' ? 5
          : Symbol('6');
        return this.value;
      }
    };
    return this;
  },
  [Symbol.iterator]() {
    return {
      next: () => ({
        value: this.next,
        done: typeof this.value === 'symbol'
      })
    };
  }
};

// Function that creates hidden type dependencies
const typeChain = (init = 0) => {
  const chain = {
    value: init,
    map(fn) {
      this.value = fn(this.value);
      return this;
    },
    then(fn) {
      return this.value?.then?.(fn) ?? typeChain(fn(this.value));
    }
  };

  return new Proxy(chain, {
    get(target, prop) {
      if (prop === Symbol.iterator) {
        return function*() {
          let current = target.value;
          while (current != null) {
            yield current;
            current = Object(current).next;
          }
        };
      }
      if (prop in target) return target[prop];
      return (...args) => {
        const method = target.value?.[prop];
        return typeChain(
          typeof method === 'function'
            ? method.apply(target.value, args)
            : undefined
        );
      };
    }
  });
};

// Recursive type system stress test
class RecursiveWrapper {
  static instances = new WeakSet();

  constructor(value) {
    if (RecursiveWrapper.instances.has(value)) {
      return value;
    }
    this.value = value;
    RecursiveWrapper.instances.add(this);

    // Create recursive getters dynamically
    Object.defineProperty(this, 'wrapped', {
      get() {
        return new RecursiveWrapper(this);
      }
    });
  }

  valueOf() {
    try {
      return this.value?.valueOf?.() ?? this.value;
    } catch {
      return this;
    }
  }

  toString() {
    try {
      return String(this.valueOf());
    } catch {
      return '[RecursiveWrapper]';
    }
  }
}

// Generator that produces values with interdependent types
function* typeGenerator() {
  let state = { count: 0, last: null };

  while (true) {
    switch (state.count++ % 3) {
      case 0:
        state.last = yield state.last ?? 0;
        break;
      case 1:
        state.last = yield Promise.resolve(state.last)
          .then(x => x?.toString?.() ?? '');
        break;
      case 2:
        state.last = yield new RecursiveWrapper(state.last);
        break;
    }

    if (state.count > 10) {
      return state.last;
    }
  }
}

// Object with hidden property access side effects
const sideEffector = {
  _value: 0,
  get value() {
    return ++this._value;
  },
  set value(x) {
    this._value = x > this._value ? -x : ~x;
  }
};

// Create circular references with type implications
const circular1 = { val: 1 };
const circular2 = { val: '2' };
circular1.next = circular2;
circular2.next = circular1;

Object.defineProperties(circular1, {
  computed: {
    get() {
      return this.next.val + this.val;
    }
  }
});

Object.defineProperties(circular2, {
  computed: {
    get() {
      return this.next.val * this.val;
    }
  }
});

// Function that breaks type inference through WeakMap
const weakMapper = (() => {
  const private1 = new WeakMap();
  const private2 = new WeakMap();

  return (obj) => {
    if (!private1.has(obj)) {
      private1.set(obj, {
        value: typeof obj === 'number' ? String(obj) : Number(obj)
      });
    }
    if (!private2.has(obj)) {
      private2.set(obj, new Set([obj, private1.get(obj)]));
    }
    return [...private2.get(obj)][Math.random() > 0.5 ? 0 : 1];
  };
})();

// Mixing generators and async iteration
async function* mixedGenerator() {
  const gen = typeGenerator();
  let result = gen.next();

  while (!result.done) {
    const value = result.value;
    result = gen.next(
      await Promise.resolve(value).then(weakMapper)
    );
    yield typeof value === 'object' ? { ...value } : value;
  }
}

// Usage that combines multiple edge cases
(async () => {
  const poly = polymorph({
    a: 1,
    b: "2",
    c: false,
    d: [null, undefined, Symbol()],
    e: shapeShifter
  });

  const chain = typeChain(poly)
    .map(x => new RecursiveWrapper(x))
    .map(Object)
    .toString()
    .repeat(2)
    .split('')
    .filter(Boolean);

  for await (const value of mixedGenerator()) {
    try {
      const result = chain
        .map(() => value)
        .then(weakMapper);

      console.log(await result);
    } catch (e) {
      // Swallow errors to continue iteration
    }
  }

  // Create type confusion
  circular1.next.next.next.val += sideEffector.value++;
  circular2.next.next.computed *= await Promise.resolve(shapeShifter.next);
})().catch(console.error);

// Additional type system stress tests
const typeStressTests = {
  mixedArrays: [1, "2", false, [3n, Symbol(), null]],

  objectWithGetters: {
    get a() { return this.b; },
    get b() { return this.c; },
    get c() { return this.a; },
    toString() { return this.a; }
  },

  infiniteIterator: {
    *[Symbol.iterator]() {
      let i = 0;
      while (true) {
        yield this[i++ % 4];
      }
    },
    0: 1,
    1: "2",
    2: { 3: 4 },
    3: [5, 6, 7]
  },

  promiseChain: Promise.resolve(1)
    .then(x => String(x))
    .then(x => [x])
    .then(x => ({ x }))
    .then(x => x.x[0])
    .then(Number),

  bigIntMixer: {
    value: 0n,
    [Symbol.toPrimitive](hint) {
      this.value += 1n;
      return hint === 'number'
        ? Number(this.value)
        : hint === 'string'
        ? String(this.value)
        : this.value;
    }
  }
};

// More type coercion edge cases
const coercionTests = [
  // Array to primitive coercion chains
  [].valueOf().toString.call([1,2,3]),
  Array(3).fill().map((_, i) => i + 1).join(''),

  // Number-string boundary cases
  ~~(0.1 + 0.2),
  1 + +"1.1" + "1" + 1,

  // Object to primitive conversions
  { toString: () => 1, valueOf: () => "2" } + 3,

  // Nested template literal type conversions
  `${`${1}${true}`}${null}${undefined}`,

  // BigInt and Number interaction
  BigInt(Number.MAX_SAFE_INTEGER) + 1n,

  // Symbol to string prevention
  String(Symbol('test')).includes('test'),

  // Sparse array edge cases
  Array(5).fill().map((_, i) => i)[3],

  // Object property type mixing
  Object.assign({}, { get a() { return 1; } }).a
];

// Test the type stress cases
Object.entries(typeStressTests).forEach(([name, test]) => {
  try {
    console.log(`${name}:`,
      test?.toString?.() ?? String(test));
  } catch (e) {
    console.error(`${name} error:`, e);
  }
});
