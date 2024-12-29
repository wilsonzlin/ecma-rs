// Proxy and Reflect shenanigans
const createTrapAll = () => {
  const handler = new Proxy({}, {
    get: (target, prop) => (...args) => {
      console.log(`Trapped: ${String(prop)}`);
      return Reflect[prop]?.(...args);
    }
  });
  return new Proxy({}, handler);
};

// Prototype pollution via __proto__
const dangerousExtend = (target, source) => {
  for (let key in source) {
    if (key === '__proto__') {
      Object.setPrototypeOf(target, source[key]);
    } else {
      target[key] = source[key];
    }
  }
  return target;
};

// Tagged template literal with custom interpolation
function sql(strings, ...keys) {
  return {
    text: strings.reduce((prev, curr, i) =>
      `${prev}$${i}${curr}`),
    values: keys
  };
}

// Generator with infinite sequence and Symbol.iterator
const fibGen = function*() {
  let prev = 0n, curr = 1n;
  try {
    while (true) {
      yield curr;
      [prev, curr] = [curr, prev + curr];
    }
  } finally {
    console.log("Generator cleanup");
  }
};

// Mixing primitive and object string operations
const stringMixer = str => {
  'use strict';
  const primitive = String(str);
  const object = new String(str);

  // Intentionally weird coercions
  object.valueOf = () => undefined;
  object.toString = () => null;

  return {
    primitive,
    object,
    equals: primitive == object,
    strictEquals: primitive === object,
    addition: primitive + object,
    comparison: primitive < object
  };
};

// Property descriptor manipulation
const descriptorTricks = {
  setup() {
    // Non-configurable but writable property
    Object.defineProperty(this, 'trapped', {
      value: 1,
      writable: true,
      configurable: false
    });

    // Getter that changes behavior after first access
    let accessed = false;
    Object.defineProperty(this, 'dynamic', {
      get() {
        if (!accessed) {
          accessed = true;
          return 'first';
        }
        return 'subsequent';
      },
      configurable: true
    });

    // Setter that prevents its own modification
    Object.defineProperty(this, 'lockdown', {
      set(value) {
        Object.defineProperty(this, 'lockdown', {
          value,
          writable: false,
          configurable: false
        });
      },
      configurable: true
    });
  }
};

// WeakRef and FinalizationRegistry example
const registry = new FinalizationRegistry(held => {
  console.log('Cleaned up:', held);
});

const createWeakHolder = () => {
  const obj = { data: new Array(1e6).fill(0) };
  const weak = new WeakRef(obj);
  registry.register(obj, 'large array', weak);
  return weak;
};

// Async Iterator with Symbol.asyncIterator
const asyncCounter = {
  start: 0,
  end: 5,
  [Symbol.asyncIterator]() {
    return {
      current: this.start,
      end: this.end,
      async next() {
        await new Promise(resolve => setTimeout(resolve, 100));
        if (this.current < this.end) {
          return { done: false, value: this.current++ };
        }
        return { done: true };
      }
    };
  }
};

// Global scope pollution and implicit globals
(function() {
  'use strict';
  try {
    delete Object.prototype;  // Should throw in strict mode
  } catch (e) {
    notDefined = "I'm an implicit global!";  // Should throw in strict mode
  }
})();

// Arguments object and default parameter side effects
function argumentsTricks(a = b, b = 1) {
  arguments[0] = 100;
  b = 200;
  console.log(a, b, arguments[0]);
  return arguments.callee; // Should throw in strict mode
}

// Label and continue/break across blocks
outer: {
  inner: {
    try {
      break outer;
    } finally {
      console.log('Finally runs before break');
    }
    console.log('Never runs');
  }
}

// Mixing async and sync iterations
async function* asyncGen() {
  yield* [1, 2, 3];
  yield* (async function*() {
    await new Promise(r => setTimeout(r, 0));
    yield* fibGen();
  })();
}

// RegExp with lookbehind and named capture groups
const regexTricks = {
  palindrome: /(?<=\b)(\w)(?:(?<=(.)\1\2)\w)*\1(?=\b)/,
  namedGroups: /(?<year>\d{4})-(?<month>\d{2})-(?<day>\d{2})/u,
  unicodeProp: /\p{Script=Hebrew}/u,
  recursion: /\((?:[^()]++|(?R))*\)/
};

// Array and TypedArray mixing
const arrayMixer = () => {
  const arr = [1, 2, 3];
  const uint8 = new Uint8Array(arr);
  const float64 = new Float64Array(uint8.buffer);

  // Detached buffer operations
  const transferred = uint8.buffer;
  const worker = new Worker('data:,');
  worker.postMessage('', [transferred]);

  try {
    float64[0] = 1;  // Should throw - detached buffer
  } catch (e) {
    console.log('Detached buffer access:', e);
  }
};

// Mixing regular and arrow functions with 'this'
const thisBinding = {
  prop: 'outer',
  method() {
    (() => {
      (function() {
        console.log(this?.prop);
      })();
    })();
  }
};

// Error stack manipulation
const errorTricks = () => {
  const err = new Error('original');
  err.stack = 'manipulated stack';
  throw Object.assign(err, {
    get name() {
      return 'DynamicError';
    }
  });
};

// Promise resolution tricks
const promiseTricks = async () => {
  const circular = Promise.resolve();
  circular.then(() => circular);

  const rejected = Promise.reject(new Error('rejected'));
  rejected.catch(() => {});  // Prevent unhandled rejection

  const race = Promise.race([
    new Promise(r => setTimeout(r, 100, 'timeout')),
    Promise.resolve('instant'),
    rejected
  ]);

  try {
    await race;
  } catch {
    // Handle rejection
  }
};

// Module-like IIFE with circular dependencies
const module = (() => {
  const exports = {};

  exports.a = () => exports.b();
  exports.b = () => exports.a();

  return exports;
})();

// Testing the edge cases
try {
  const trap = createTrapAll();
  const victim = {};
  dangerousExtend(victim, { __proto__: { poisoned: true } });

  const query = sql`SELECT * FROM users WHERE id = ${1} OR name = ${'test'}`;

  const fib = fibGen();
  const first10 = Array.from({ length: 10 }, () => fib.next().value);

  const str = stringMixer('test');

  Object.create(descriptorTricks).setup();

  const weak = createWeakHolder();

  for await (const num of asyncCounter) {
    console.log(num);
  }

  argumentsTricks(5);

  const mixed = arrayMixer();

  thisBinding.method();

  await promiseTricks();

} catch (e) {
  console.log('Expected error:', e);
}
