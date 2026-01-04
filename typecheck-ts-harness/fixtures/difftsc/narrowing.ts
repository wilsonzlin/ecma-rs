class Box {}

function pick(x: { value: string } | { other: number }) {
  if ("value" in x) {
    return x.value;
  }
  return x.other;
}

function onlyObjects(val: object | number) {
  if (val instanceof Box) {
    return val;
  }
  return val;
}

function assertStr(x: string | number): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("bad");
  }
}

function useAssert(val: string | number) {
  assertStr(val);
  return val;
}

type Pickable = { value: string } | { other: number };

function pickAlias(x: Pickable) {
  if ("value" in x) {
    const v: string = x.value;
    return v;
  }
  const o: number = x.other;
  return o;
}

type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; size: number };

function shapeSizeSwitch(shape: Shape) {
  switch (shape.kind) {
    case "circle": {
      const r: number = shape.radius;
      return r;
    }
    case "square": {
      const s: number = shape.size;
      return s;
    }
  }
  return 0;
}

function shapeSizeEquality(shape: Shape) {
  if (shape.kind === "circle") {
    const r: number = shape.radius;
    return r;
  }
  const s: number = shape.size;
  return s;
}

function optionalChainNullishCoalesce(x: { value: number } | undefined) {
  if (x?.value ?? false) {
    const v: number = x.value;
    return v;
  }
  return 0;
}
