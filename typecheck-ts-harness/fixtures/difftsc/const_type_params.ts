function id<T>(value: T) {
  return value;
}

function idConst<const T>(value: T) {
  return value;
}

export const normalTuple = id([1, 2, 3]);
                    // ^?
export const constTuple = idConst([1, 2, 3]);
                   // ^?

export const normalObj = id({ a: 1, b: "x" });
                  // ^?
export const constObj = idConst({ a: 1, b: "x" });
                 // ^?

export const ok: typeof constObj = { a: 1, b: "x" };

// Diagnostic mismatch case: `const` type parameters should preserve literal types.
export const bad: typeof constObj = { a: 2, b: "no" };

function narrowPair<const T extends readonly [1, 2] | readonly [3, 4]>(value: T) {
  return value;
}

export const unionTuple = narrowPair([1, 2]);
                   // ^?
