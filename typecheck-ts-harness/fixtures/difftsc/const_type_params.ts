function asConst<const T>(value: T): T {
  return value;
}

export const inferred = asConst({ a: 1, b: "ok" });
             // ^?

export const ok: typeof inferred = { a: 1, b: "ok" };

// Diagnostic mismatch case: `const` type parameters should preserve literal types.
export const bad: typeof inferred = { a: 2, b: "no" };
