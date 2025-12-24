const obj = { a: 1, b: "x" };
const nested = { inner: { value: true } };

// expect-def-type: obj = {a: number, b: string}
// expect-def-type: nested = {inner: {value: boolean}}
