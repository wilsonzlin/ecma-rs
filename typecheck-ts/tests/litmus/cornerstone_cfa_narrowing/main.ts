// Cornerstone: control-flow narrowing as core language behavior
// (wiki/theory/compiler-theory.md § The TypeScript cornerstones)
//
// typeof / discriminant / truthiness must refine types at uses.

function typeofNarrow(x: string | number) {
  if (typeof x === "string") {
    const s = x;
    return s;
  }
  return x;
}
// expect-expr-type: s; = string

function discriminant(
  shape: { kind: "square"; size: number } | { kind: "circle"; radius: number },
) {
  if (shape.kind === "square") {
    return shape.size;
  }
  return shape.radius;
}
// expect-expr-type: shape.size; = number
// expect-expr-type: shape.radius; = number

function truthyNarrow(x: string | null) {
  if (x) {
    const s = x;
    return s;
  }
  return "";
}
// expect-expr-type: s; = string
