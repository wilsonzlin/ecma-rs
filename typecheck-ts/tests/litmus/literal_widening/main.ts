const one = 1;
// expect-def-type: one = 1

let widened = 1;
// expect-def-type: widened = number

const literalStr = "hi";
// expect-def-type: literalStr = "hi"

let widenedStr = "hi";
// expect-def-type: widenedStr = string

const obj = { value: 1 };
// expect-def-type: obj = { value: number }

const objConst = { value: 1 } as const;
// expect-def-type: objConst = { readonly value: 1 }

let contextual: { literal: 1 } = { literal: 1 };
// expect-def-type: contextual = { literal: 1 }

const arr = [1, 2];
// expect-def-type: arr = number[]

const tupleConst = [1, 2] as const;
// expect-def-type: tupleConst = readonly [1, 2]

const satisfies = { tag: "a" } satisfies { tag: "a" | "b" };
// expect-def-type: satisfies = { tag: "a" }
