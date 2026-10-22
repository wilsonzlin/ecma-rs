// Cornerstone: overload selection
// (wiki/theory/compiler-theory.md § The TypeScript cornerstones)
//
// Ranked trial checking picks the best matching signature; no match → diagnostic.

function pick(x: string): string;
function pick(x: number): number;
function pick(x: string | number): string | number {
  return x;
}

const s = pick("hi");
const n = pick(1);
// expect-def-type: s = string
// expect-def-type: n = number

const bad = pick(true);
// expect-diagnostic: TS2769 "true"
