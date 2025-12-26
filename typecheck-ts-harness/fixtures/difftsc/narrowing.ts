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
