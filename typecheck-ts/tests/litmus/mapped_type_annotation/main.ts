const mapped: { [K in "a" | "b"]: number } = { a: 1, b: 2 };

// expect-def-type: mapped = unknown
