// Cornerstone: freshness / excess-property checks
const direct: { foo: number } = { foo: 1, bar: 2 };
const indexed: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };
const tmp = { foo: 1, bar: 2 };
const viaVar: { foo: number } = tmp;
