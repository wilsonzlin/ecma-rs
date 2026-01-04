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
