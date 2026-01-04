function pick(x: { value: string } | { other: number }) {
  if ("value" in x) {
    return x.value;
  }
  return x.other;
}

// expect-expr-type: .value; = string

function assertNumber(val: string | number): asserts val is number {
  if (typeof val === "string") {
    throw new Error("bad");
  }
}

function useAssert(v: string | number) {
  assertNumber(v);
  return v;
}

// expect-def-type: useAssert = (v: string | number) => number

function Box() {}

function onlyObjects(val: object | number) {
  if (val instanceof Box) {
    const inner = val;
    return inner;
  }
  return val;
}

// expect-expr-type: inner; = object

function area(shape: { kind: "square", size: number } | { kind: "circle", radius: number }) {
  switch (shape.kind) {
    case "square":
      return shape.size;
    case "circle":
      return shape.radius;
  }
}

// expect-expr-type: shape.size; = number
// expect-expr-type: shape.radius; = number

function shortCircuit(val: string | null) {
  if (val && typeof val === "string") {
    const narrowed = val;
    return narrowed;
  }
  return val;
}

// expect-expr-type: narrowed; = string

function isString(val: string | number): val is string {
  return typeof val === "string";
}

function guardUse(input: string | number) {
  if (isString(input)) {
    const refined = input;
    return refined;
  }
  return input;
}

// expect-expr-type: refined; = string
