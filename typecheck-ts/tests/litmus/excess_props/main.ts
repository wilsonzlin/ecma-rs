const direct: { foo: number } = { foo: 1, bar: 2 };
// expect-diagnostic: TC0006 "direct: { foo: number } = { foo: 1, bar: 2 }"

const indexed: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };

const tmp = { foo: 1, bar: 2 };
const viaVar: { foo: number } = tmp;

const asserted: { foo: number } = ({ foo: 1, bar: 2 } as { foo: number });

const unionOk: { foo: number } | { bar: number } = { foo: 1 };
const unionBad: { foo: number } | { bar: number } = { foo: 1, bar: 2 };
// expect-diagnostic: TC0006 "unionBad: { foo: number } | { bar: number } = { foo: 1, bar: 2 }"

function make(): { foo: number } {
  return { foo: 1, bar: 2 };
}
// expect-diagnostic: TC0006 "return { foo: 1, bar: 2 }"

function takes(obj: { foo: number }) {}
takes({ foo: 1, bar: 2 });
// expect-diagnostic: TC0006 "takes({ foo: 1, bar: 2 });"

type Mapped = { [K in string]: number };
const mapped: Mapped = { foo: 1, bar: 2, baz: 3 };

const unionIndex: { [key: string | number]: number } = { foo: 1, 0: 2 };
