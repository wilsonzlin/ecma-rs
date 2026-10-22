// Cornerstone: keyof duality + mapped remapping
type A = { a: number; shared: string };
type B = { b: boolean; shared: string };

// Duality proved by diagnostics (common-only vs all keys).
const keysUnion: keyof (A | B) = "shared";
const keysUnionBad: keyof (A | B) = "a";
const keysInterA: keyof (A & B) = "a";
const keysInterBad: keyof (A & B) = "missing";

// Mapped remapping: export the shape that already matches rust↔tsc display.
export const remapped: { [K in "a" | "b" as `${K}Id`]: number } = {
  aId: 1,
  bId: 2,
};
