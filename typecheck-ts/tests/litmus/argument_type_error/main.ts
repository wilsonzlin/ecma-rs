function toNumber(value: number): number {
  return value;
}

const bad = toNumber("oops");

// expect-def-type: toNumber = (number) -> number
// expect-def-type: bad = number
// expect-diagnostic: none "\"oops\""
