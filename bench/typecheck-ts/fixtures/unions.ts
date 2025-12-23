type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; size: number }
  | { kind: "polygon"; edges: number[] }
  | { kind: "line"; from: [number, number]; to: [number, number] };

export function area(shape: Shape) {
  switch (shape.kind) {
    case "circle":
      return Math.PI * shape.radius * shape.radius;
    case "square":
      return shape.size * shape.size;
    case "polygon":
      return shape.edges.reduce((acc, edge) => acc + edge, 0);
    default:
      return 0;
  }
}

type Deep = (string | number | boolean | null | undefined | bigint | symbol)[];
export const deepValue: Deep = [
  "a",
  1,
  true,
  null,
  undefined,
  10n,
  Symbol("x"),
];
