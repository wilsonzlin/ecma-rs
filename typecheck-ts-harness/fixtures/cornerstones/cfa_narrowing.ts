// Cornerstone: control-flow narrowing
export function typeofNarrow(x: string | number) {
  if (typeof x === "string") {
    return x.length;
  }
  return x.toFixed(1);
}

export function discriminant(
  shape: { kind: "square"; size: number } | { kind: "circle"; radius: number },
) {
  if (shape.kind === "square") {
    return shape.size;
  }
  return shape.radius;
}
