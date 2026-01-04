function add(a: number, b: number): number {
  return a + b;
}

const result = add(1);

// expect-def-type: add = (a: number, b: number) => number
// expect-expr-type: "(1)" = number
// expect-diagnostic: none "(1)"
