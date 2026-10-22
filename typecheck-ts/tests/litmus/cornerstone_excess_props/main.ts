// Cornerstone: object-literal freshness / excess-property checks
// (wiki/theory/compiler-theory.md § The TypeScript cornerstones)
//
// Fresh literals get excess-property checks; index signatures, assertions,
// and intermediate variables suppress them.

const direct: { foo: number } = { foo: 1, bar: 2 };
// expect-diagnostic: TS2353 "bar"

const indexed: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };

const tmp = { foo: 1, bar: 2 };
const viaVar: { foo: number } = tmp;

const asserted: { foo: number } = { foo: 1, bar: 2 } as { foo: number };
