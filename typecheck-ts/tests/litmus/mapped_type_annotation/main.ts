const mapped: { [K in "a" | "b"]: number } = { a: 1, b: 2 };

type Remapped = { [K in "a" | "b" as `${K}Id`]: number };
const remapped: Remapped = { aId: 1, bId: 2 };

// expect-def-type: mapped = { a: number; b: number }
