export function pickValue(value: string | number) {
  if (typeof value === "string") {
    const narrowed = value;
    //            ^?
    return narrowed;
  }
  return value;
}

type Foo = { kind: "foo"; value: string };
type Bar = { kind: "bar"; value: number };
type Shape = Foo | Bar;

function pickShapeValue(shape: Shape) {
  if (shape.kind === "foo") {
    shape.value/*^?*/;
    return shape.value;
  }

  shape.value/*^?*/;
  return shape.value;
}

function pickShapeValueSwitch(shape: Shape) {
  switch (shape.kind) {
    case "foo":
      shape.value/*^?*/;
      break;
    case "bar":
      shape.value/*^?*/;
      break;
  }
}

function pickIn(x: { value: string } | { other: number }) {
  if ("value" in x) {
    x.value/*^?*/;
  } else {
    x.other/*^?*/;
  }
}

type Box = { value: string };
declare const Box: new () => Box;

function pickInstance(val: object) {
  if (val instanceof Box) {
    val/*^?*/;
    val.value;
  }
}

function optionalChainNarrows(x: { foo: string } | undefined) {
  if (x?.foo) {
    x/*^?*/;
    x.foo;
  }
}

function nullishCoalescingNarrowsRhs(x: string | null | undefined) {
  x ?? x/*^?*/;
}

function optionalChainMemberType(x: { a: { b: number } } | null) {
  x?.a.b/*^?*/;
}

function optionalChainCallType(x: { a: { b: () => number } } | null) {
  x?.a.b()/*^?*/;
}

function optionalCallType(x: (() => number) | null) {
  x?.()/*^?*/;
}

function optionalChainEqualityNarrows(x: { a: { b: number } } | null, y: number) {
  if (x?.a.b === y) {
    x/*^?*/;
  }
  x/*^?*/;
}

function optionalChainInequalityUndefinedNarrows(
  x: { a: { b: () => number } } | null,
  y: number,
) {
  if (x?.a.b() !== undefined) {
    x/*^?*/;
  }
  if (x?.a.b() !== y) {
    x/*^?*/;
  }
}

type Tagged =
  | { kind: "a"; a: number }
  | { kind: "b"; b: number };

function pickTagged(x: Tagged) {
  if (x.kind === "a") {
    const a: number = x.a;
    return a;
  }
  const b: number = x.b;
  return b;
}

function optionalChainNullishCoalesce(x: { value: number } | undefined) {
  if (x?.value ?? false) {
    const v: number = x.value;
    return v;
  }
  return 0;
}
