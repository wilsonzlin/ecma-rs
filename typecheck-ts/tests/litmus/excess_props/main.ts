const direct: { foo: number } = { foo: 1, bar: 2 };
// expect-diagnostic: TC0006 "direct: { foo: number } = { foo: 1, bar: 2 }"

const indexed: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };

const tmp = { foo: 1, bar: 2 };
const viaVar: { foo: number } = tmp;

const asserted: { foo: number } = ({ foo: 1, bar: 2 } as { foo: number });

function make(): { foo: number } {
  return { foo: 1, bar: 2 };
}
// expect-diagnostic: TC0006 "return { foo: 1, bar: 2 }"
